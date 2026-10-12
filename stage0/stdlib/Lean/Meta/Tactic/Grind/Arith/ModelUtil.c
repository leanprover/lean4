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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getGeneration(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_finalizeModel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(lean_object* v_a_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_4_) == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v_key_6_; lean_object* v_value_7_; lean_object* v_tail_8_; uint8_t v___x_9_; 
v_key_6_ = lean_ctor_get(v_x_4_, 0);
v_value_7_ = lean_ctor_get(v_x_4_, 1);
v_tail_8_ = lean_ctor_get(v_x_4_, 2);
v___x_9_ = lean_expr_eqv(v_key_6_, v_a_3_);
if (v___x_9_ == 0)
{
v_x_4_ = v_tail_8_;
goto _start;
}
else
{
lean_object* v___x_11_; 
lean_inc(v_value_7_);
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v_value_7_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg___boxed(lean_object* v_a_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec_ref(v_a_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(lean_object* v_m_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_buckets_17_; lean_object* v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; uint64_t v___x_21_; uint64_t v_fold_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_buckets_17_ = lean_ctor_get(v_m_15_, 1);
v___x_18_ = lean_array_get_size(v_buckets_17_);
v___x_19_ = l_Lean_Expr_hash(v_a_16_);
v___x_20_ = 32ULL;
v___x_21_ = lean_uint64_shift_right(v___x_19_, v___x_20_);
v_fold_22_ = lean_uint64_xor(v___x_19_, v___x_21_);
v___x_23_ = 16ULL;
v___x_24_ = lean_uint64_shift_right(v_fold_22_, v___x_23_);
v___x_25_ = lean_uint64_xor(v_fold_22_, v___x_24_);
v___x_26_ = lean_uint64_to_usize(v___x_25_);
v___x_27_ = lean_usize_of_nat(v___x_18_);
v___x_28_ = ((size_t)1ULL);
v___x_29_ = lean_usize_sub(v___x_27_, v___x_28_);
v___x_30_ = lean_usize_land(v___x_26_, v___x_29_);
v___x_31_ = lean_array_uget_borrowed(v_buckets_17_, v___x_30_);
v___x_32_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_16_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg___boxed(lean_object* v_m_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_33_, v_a_34_);
lean_dec_ref(v_a_34_);
lean_dec_ref(v_m_33_);
return v_res_35_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(lean_object* v_a_36_, lean_object* v_v_37_, lean_object* v_other_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_a_36_, v_other_38_);
if (lean_obj_tag(v___x_39_) == 1)
{
lean_object* v_val_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_val_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v___x_39_, 1);
v___x_41_ = l_Rat_ofInt(v_v_37_);
v___x_42_ = l_instDecidableEqRat_decEq(v_val_40_, v___x_41_);
lean_dec_ref(v___x_41_);
lean_dec(v_val_40_);
if (v___x_42_ == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
uint8_t v___x_45_; 
lean_dec(v___x_39_);
lean_dec(v_v_37_);
v___x_45_ = 1;
return v___x_45_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_36_ = stack[0].m_obj;
lean_object* v_v_37_ = stack[1].m_obj;
lean_object* v_other_38_ = stack[2].m_obj;
uint8_t v_res_46_;
v_res_46_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_36_, v_v_37_, v_other_38_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object* v_a_47_, lean_object* v_v_48_, lean_object* v_other_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_47_, v_v_48_, v_other_49_);
lean_dec_ref(v_other_49_);
lean_dec_ref(v_a_47_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object* v_00_u03b2_52_, lean_object* v_m_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_53_, v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object* v_00_u03b2_56_, lean_object* v_m_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_56_, v_m_57_, v_a_58_);
lean_dec_ref(v_a_58_);
lean_dec_ref(v_m_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object* v_00_u03b2_60_, lean_object* v_a_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object* v_00_u03b2_64_, lean_object* v_a_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_64_, v_a_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec_ref(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object* v_goal_83_, lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_v_86_, lean_object* v_as_x27_87_, lean_object* v_b_88_){
_start:
{
if (lean_obj_tag(v_as_x27_87_) == 0)
{
lean_dec(v_v_86_);
lean_inc_ref(v_b_88_);
return v_b_88_;
}
else
{
lean_object* v_head_89_; lean_object* v_tail_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___y_94_; uint8_t v___y_95_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_head_89_ = lean_ctor_get(v_as_x27_87_, 0);
v_tail_90_ = lean_ctor_get(v_as_x27_87_, 1);
v___x_91_ = lean_box(0);
v___x_92_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_89_);
v___x_100_ = l_Lean_Expr_cleanupAnnotations(v_head_89_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_dec_ref(v___x_100_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v_arg_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_arg_103_ = lean_ctor_get(v___x_100_, 1);
lean_inc_ref(v_arg_103_);
v___x_104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_105_ = l_Lean_Expr_isApp(v___x_104_);
if (v___x_105_ == 0)
{
lean_dec_ref(v___x_104_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v_arg_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_arg_107_ = lean_ctor_get(v___x_104_, 1);
lean_inc_ref(v_arg_107_);
v___x_108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_104_);
v___x_109_ = l_Lean_Expr_isApp(v___x_108_);
if (v___x_109_ == 0)
{
lean_dec_ref(v___x_108_);
lean_dec_ref(v_arg_107_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_108_);
v___x_112_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_113_ = l_Lean_Expr_isConstOf(v___x_111_, v___x_112_);
lean_dec_ref(v___x_111_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_arg_107_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_83_, v_head_89_);
if (lean_obj_tag(v___x_115_) == 1)
{
lean_object* v_val_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_val_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_118_ = l_Lean_Expr_isConstOf(v_val_116_, v___x_117_);
lean_dec(v_val_116_);
if (v___x_118_ == 0)
{
lean_dec_ref(v_arg_107_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_83_, v_arg_107_);
lean_dec_ref(v_arg_107_);
if (lean_obj_tag(v___x_120_) == 1)
{
lean_object* v_val_121_; lean_object* v___x_122_; 
v_val_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_83_, v_arg_103_);
lean_dec_ref(v_arg_103_);
if (lean_obj_tag(v___x_122_) == 1)
{
lean_object* v_val_123_; uint8_t v___y_125_; uint8_t v___y_130_; uint8_t v___x_132_; 
v_val_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_132_ = lean_expr_eqv(v_val_121_, v_e_84_);
if (v___x_132_ == 0)
{
v___y_130_ = v___x_132_;
goto v___jp_129_;
}
else
{
uint8_t v___x_133_; 
lean_inc(v_v_86_);
v___x_133_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_85_, v_v_86_, v_val_123_);
if (v___x_133_ == 0)
{
v___y_130_ = v___x_118_;
goto v___jp_129_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = 0;
v___y_125_ = v___x_134_;
goto v___jp_124_;
}
}
v___jp_124_:
{
uint8_t v___x_126_; 
v___x_126_ = lean_expr_eqv(v_val_123_, v_e_84_);
lean_dec(v_val_123_);
if (v___x_126_ == 0)
{
lean_dec(v_val_121_);
v___y_94_ = v___y_125_;
v___y_95_ = v___x_126_;
goto v___jp_93_;
}
else
{
uint8_t v___x_127_; 
lean_inc(v_v_86_);
v___x_127_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_85_, v_v_86_, v_val_121_);
lean_dec(v_val_121_);
if (v___x_127_ == 0)
{
v___y_94_ = v___y_125_;
v___y_95_ = v___x_118_;
goto v___jp_93_;
}
else
{
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
}
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
v___y_125_ = v___y_130_;
goto v___jp_124_;
}
else
{
lean_object* v___x_131_; 
lean_dec(v_val_123_);
lean_dec(v_val_121_);
lean_dec(v_v_86_);
v___x_131_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6));
return v___x_131_;
}
}
}
else
{
lean_dec(v___x_122_);
lean_dec(v_val_121_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
}
else
{
lean_dec(v___x_120_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
}
}
else
{
lean_dec(v___x_115_);
lean_dec_ref(v_arg_107_);
lean_dec_ref(v_arg_103_);
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
}
}
}
}
v___jp_93_:
{
if (v___y_95_ == 0)
{
v_as_x27_87_ = v_tail_90_;
v_b_88_ = v___x_92_;
goto _start;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_v_86_);
v___x_97_ = lean_box(v___y_94_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_91_);
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_138_, lean_object* v_e_139_, lean_object* v_a_140_, lean_object* v_v_141_, lean_object* v_as_x27_142_, lean_object* v_b_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_138_, v_e_139_, v_a_140_, v_v_141_, v_as_x27_142_, v_b_143_);
lean_dec_ref(v_b_143_);
lean_dec(v_as_x27_142_);
lean_dec_ref(v_a_140_);
lean_dec_ref(v_e_139_);
lean_dec_ref(v_goal_138_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_145_, lean_object* v_vals_146_, lean_object* v_i_147_, lean_object* v_k_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_get_size(v_keys_145_);
v___x_150_ = lean_nat_dec_lt(v_i_147_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec(v_i_147_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_k_x27_152_; size_t v___x_153_; size_t v___x_154_; uint8_t v___x_155_; 
v_k_x27_152_ = lean_array_fget_borrowed(v_keys_145_, v_i_147_);
v___x_153_ = lean_ptr_addr(v_k_148_);
v___x_154_ = lean_ptr_addr(v_k_x27_152_);
v___x_155_ = lean_usize_dec_eq(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_i_147_, v___x_156_);
lean_dec(v_i_147_);
v_i_147_ = v___x_157_;
goto _start;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_array_fget_borrowed(v_vals_146_, v_i_147_);
lean_dec(v_i_147_);
lean_inc(v___x_159_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_k_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_161_, v_vals_162_, v_i_163_, v_k_164_);
lean_dec_ref(v_k_164_);
lean_dec_ref(v_vals_162_);
lean_dec_ref(v_keys_161_);
return v_res_165_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_166_, size_t v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_es_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v_j_173_; lean_object* v___x_174_; 
v_es_169_ = lean_ctor_get(v_x_166_, 0);
v___x_170_ = lean_box(2);
v___x_171_ = ((size_t)31ULL);
v___x_172_ = lean_usize_land(v_x_167_, v___x_171_);
v_j_173_ = lean_usize_to_nat(v___x_172_);
v___x_174_ = lean_array_get_borrowed(v___x_170_, v_es_169_, v_j_173_);
lean_dec(v_j_173_);
switch(lean_obj_tag(v___x_174_))
{
case 0:
{
lean_object* v_key_175_; lean_object* v_val_176_; size_t v___x_177_; size_t v___x_178_; uint8_t v___x_179_; 
v_key_175_ = lean_ctor_get(v___x_174_, 0);
v_val_176_ = lean_ctor_get(v___x_174_, 1);
v___x_177_ = lean_ptr_addr(v_x_168_);
v___x_178_ = lean_ptr_addr(v_key_175_);
v___x_179_ = lean_usize_dec_eq(v___x_177_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
lean_inc(v_val_176_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_val_176_);
return v___x_181_;
}
}
case 1:
{
lean_object* v_node_182_; size_t v___x_183_; size_t v___x_184_; 
v_node_182_ = lean_ctor_get(v___x_174_, 0);
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_usize_shift_right(v_x_167_, v___x_183_);
v_x_166_ = v_node_182_;
v_x_167_ = v___x_184_;
goto _start;
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_box(0);
return v___x_186_;
}
}
}
else
{
lean_object* v_ks_187_; lean_object* v_vs_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_ks_187_ = lean_ctor_get(v_x_166_, 0);
v_vs_188_ = lean_ctor_get(v_x_166_, 1);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_187_, v_vs_188_, v___x_189_, v_x_168_);
return v___x_190_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_166_ = stack[0].m_obj;
size_t v_x_167_ = stack[1].m_num;
lean_object* v_x_168_ = stack[2].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_166_, v_x_167_, v_x_168_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
size_t v_x_1816__boxed_195_; lean_object* v_res_196_; 
v_x_1816__boxed_195_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_192_, v_x_1816__boxed_195_, v_x_194_);
lean_dec_ref(v_x_194_);
lean_dec_ref(v_x_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; uint64_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_199_ = lean_ptr_addr(v_x_198_);
v___x_200_ = ((size_t)3ULL);
v___x_201_ = lean_usize_shift_right(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_to_uint64(v___x_201_);
v___x_203_ = lean_uint64_to_usize(v___x_202_);
v___x_204_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_197_, v___x_203_, v_x_198_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_205_, v_x_206_);
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_205_);
return v_res_207_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_208_, lean_object* v_a_209_, lean_object* v_e_210_, lean_object* v_v_211_){
_start:
{
lean_object* v_toGoalState_212_; lean_object* v_parents_213_; lean_object* v___x_214_; 
v_toGoalState_212_ = lean_ctor_get(v_goal_208_, 0);
v_parents_213_ = lean_ctor_get(v_toGoalState_212_, 3);
v___x_214_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_213_, v_e_210_);
if (lean_obj_tag(v___x_214_) == 1)
{
lean_object* v_val_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_fst_219_; 
v_val_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_215_);
lean_dec(v_val_215_);
v___x_217_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_218_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_208_, v_e_210_, v_a_209_, v_v_211_, v___x_216_, v___x_217_);
lean_dec(v___x_216_);
v_fst_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_fst_219_);
lean_dec_ref(v___x_218_);
if (lean_obj_tag(v_fst_219_) == 0)
{
uint8_t v___x_220_; 
v___x_220_ = 1;
return v___x_220_;
}
else
{
lean_object* v_val_221_; uint8_t v___x_222_; 
v_val_221_ = lean_ctor_get(v_fst_219_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v_fst_219_, 1);
v___x_222_ = lean_unbox(v_val_221_);
lean_dec(v_val_221_);
return v___x_222_;
}
}
else
{
uint8_t v___x_223_; 
lean_dec(v___x_214_);
lean_dec(v_v_211_);
v___x_223_ = 1;
return v___x_223_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_208_ = stack[0].m_obj;
lean_object* v_a_209_ = stack[1].m_obj;
lean_object* v_e_210_ = stack[2].m_obj;
lean_object* v_v_211_ = stack[3].m_obj;
uint8_t v_res_224_;
v_res_224_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_208_, v_a_209_, v_e_210_, v_v_211_);
stack->m_num = v_res_224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_225_, lean_object* v_a_226_, lean_object* v_e_227_, lean_object* v_v_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_225_, v_a_226_, v_e_227_, v_v_228_);
lean_dec_ref(v_e_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_goal_225_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_235_, v_x_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_239_, lean_object* v_e_240_, lean_object* v_a_241_, lean_object* v_v_242_, lean_object* v_as_243_, lean_object* v_as_x27_244_, lean_object* v_b_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_239_, v_e_240_, v_a_241_, v_v_242_, v_as_x27_244_, v_b_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_248_, lean_object* v_e_249_, lean_object* v_a_250_, lean_object* v_v_251_, lean_object* v_as_252_, lean_object* v_as_x27_253_, lean_object* v_b_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_248_, v_e_249_, v_a_250_, v_v_251_, v_as_252_, v_as_x27_253_, v_b_254_, v_a_255_);
lean_dec_ref(v_b_254_);
lean_dec(v_as_x27_253_);
lean_dec(v_as_252_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_e_249_);
lean_dec_ref(v_goal_248_);
return v_res_256_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_257_, lean_object* v_x_258_, size_t v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_258_, v_x_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_258_ = stack[1].m_obj;
size_t v_x_259_ = stack[2].m_num;
lean_object* v_x_260_ = stack[3].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_box(0), v_x_258_, v_x_259_, v_x_260_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
size_t v_x_1975__boxed_267_; lean_object* v_res_268_; 
v_x_1975__boxed_267_ = lean_unbox_usize(v_x_265_);
lean_dec(v_x_265_);
v_res_268_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_263_, v_x_264_, v_x_1975__boxed_267_, v_x_266_);
lean_dec_ref(v_x_266_);
lean_dec_ref(v_x_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_269_, lean_object* v_keys_270_, lean_object* v_vals_271_, lean_object* v_heq_272_, lean_object* v_i_273_, lean_object* v_k_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_270_, v_vals_271_, v_i_273_, v_k_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_276_, lean_object* v_keys_277_, lean_object* v_vals_278_, lean_object* v_heq_279_, lean_object* v_i_280_, lean_object* v_k_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_276_, v_keys_277_, v_vals_278_, v_heq_279_, v_i_280_, v_k_281_);
lean_dec_ref(v_k_281_);
lean_dec_ref(v_vals_278_);
lean_dec_ref(v_keys_277_);
return v_res_282_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_a_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
else
{
lean_object* v_key_286_; lean_object* v_tail_287_; uint8_t v___x_288_; 
v_key_286_ = lean_ctor_get(v_x_284_, 0);
v_tail_287_ = lean_ctor_get(v_x_284_, 2);
v___x_288_ = lean_int_dec_eq(v_key_286_, v_a_283_);
if (v___x_288_ == 0)
{
v_x_284_ = v_tail_287_;
goto _start;
}
else
{
return v___x_288_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_283_ = stack[0].m_obj;
lean_object* v_x_284_ = stack[1].m_obj;
uint8_t v_res_290_;
v_res_290_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_283_, v_x_284_);
stack->m_num = v_res_290_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_291_, v_x_292_);
lean_dec(v_x_292_);
lean_dec(v_a_291_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_295_; lean_object* v_intZero_296_; 
v_natZero_295_ = lean_unsigned_to_nat(0u);
v_intZero_296_ = lean_nat_to_int(v_natZero_295_);
return v_intZero_296_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_buckets_299_; lean_object* v___x_300_; uint64_t v___y_302_; lean_object* v_intZero_316_; uint8_t v_isNeg_317_; 
v_buckets_299_ = lean_ctor_get(v_m_297_, 1);
v___x_300_ = lean_array_get_size(v_buckets_299_);
v_intZero_316_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_317_ = lean_int_dec_lt(v_a_298_, v_intZero_316_);
if (v_isNeg_317_ == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint64_t v___x_321_; 
v_a_318_ = lean_nat_abs(v_a_298_);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_mul(v___x_319_, v_a_318_);
lean_dec(v_a_318_);
v___x_321_ = lean_uint64_of_nat(v___x_320_);
lean_dec(v___x_320_);
v___y_302_ = v___x_321_;
goto v___jp_301_;
}
else
{
lean_object* v_abs_322_; lean_object* v_one_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint64_t v___x_328_; 
v_abs_322_ = lean_nat_abs(v_a_298_);
v_one_323_ = lean_unsigned_to_nat(1u);
v_a_324_ = lean_nat_sub(v_abs_322_, v_one_323_);
lean_dec(v_abs_322_);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_nat_mul(v___x_325_, v_a_324_);
lean_dec(v_a_324_);
v___x_327_ = lean_nat_add(v___x_326_, v_one_323_);
lean_dec(v___x_326_);
v___x_328_ = lean_uint64_of_nat(v___x_327_);
lean_dec(v___x_327_);
v___y_302_ = v___x_328_;
goto v___jp_301_;
}
v___jp_301_:
{
uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v_fold_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_303_ = 32ULL;
v___x_304_ = lean_uint64_shift_right(v___y_302_, v___x_303_);
v_fold_305_ = lean_uint64_xor(v___y_302_, v___x_304_);
v___x_306_ = 16ULL;
v___x_307_ = lean_uint64_shift_right(v_fold_305_, v___x_306_);
v___x_308_ = lean_uint64_xor(v_fold_305_, v___x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = lean_usize_of_nat(v___x_300_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v___x_310_, v___x_311_);
v___x_313_ = lean_usize_land(v___x_309_, v___x_312_);
v___x_314_ = lean_array_uget_borrowed(v_buckets_299_, v___x_313_);
v___x_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_298_, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_297_ = stack[0].m_obj;
lean_object* v_a_298_ = stack[1].m_obj;
uint8_t v_res_329_;
v_res_329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_297_, v_a_298_);
stack->m_num = v_res_329_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
uint8_t v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_m_330_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_to_int(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_336_, lean_object* v_a_337_, lean_object* v_e_338_, lean_object* v_alreadyUsed_339_, lean_object* v_next_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_339_, v_next_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
lean_inc(v_next_340_);
v___x_342_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_336_, v_a_337_, v_e_338_, v_next_340_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_344_ = lean_int_add(v_next_340_, v___x_343_);
lean_dec(v_next_340_);
v_next_340_ = v___x_344_;
goto _start;
}
else
{
return v_next_340_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_347_ = lean_int_add(v_next_340_, v___x_346_);
lean_dec(v_next_340_);
v_next_340_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_349_, lean_object* v_a_350_, lean_object* v_e_351_, lean_object* v_alreadyUsed_352_, lean_object* v_next_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_349_, v_a_350_, v_e_351_, v_alreadyUsed_352_, v_next_353_);
lean_dec_ref(v_alreadyUsed_352_);
lean_dec_ref(v_e_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_goal_349_);
return v_res_354_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_356_, v_a_357_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_356_ = stack[1].m_obj;
lean_object* v_a_357_ = stack[2].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_box(0), v_m_356_, v_a_357_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_360_, lean_object* v_m_361_, lean_object* v_a_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_360_, v_m_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_m_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_365_, lean_object* v_a_366_, lean_object* v_x_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_366_ = stack[1].m_obj;
lean_object* v_x_367_ = stack[2].m_obj;
uint8_t v_res_369_;
v_res_369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_box(0), v_a_366_, v_x_367_);
stack->m_num = v_res_369_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_370_, lean_object* v_a_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_370_, v_a_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_a_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_375_, lean_object* v_a_376_, lean_object* v_e_377_, lean_object* v_next_378_, lean_object* v_alreadyUsed_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_375_, v_a_376_, v_e_377_, v_alreadyUsed_379_, v_next_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_381_, lean_object* v_a_382_, lean_object* v_e_383_, lean_object* v_next_384_, lean_object* v_alreadyUsed_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_381_, v_a_382_, v_e_383_, v_next_384_, v_alreadyUsed_385_);
lean_dec_ref(v_alreadyUsed_385_);
lean_dec_ref(v_e_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_goal_381_);
return v_res_386_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_472_){
_start:
{
uint8_t v___y_479_; uint8_t v___x_512_; 
lean_inc_ref(v_e_472_);
v___x_512_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_472_);
if (v___x_512_ == 0)
{
uint8_t v___x_513_; 
lean_inc_ref(v_e_472_);
v___x_513_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_472_);
v___y_479_ = v___x_513_;
goto v___jp_478_;
}
else
{
v___y_479_ = v___x_512_;
goto v___jp_478_;
}
v___jp_473_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_475_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4));
v___x_477_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_476_);
lean_dec_ref(v_e_472_);
return v___x_477_;
}
else
{
lean_dec_ref(v_e_472_);
return v___x_475_;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7));
v___x_481_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10));
v___x_483_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13));
v___x_485_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16));
v___x_487_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19));
v___x_489_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22));
v___x_491_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25));
v___x_493_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28));
v___x_495_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31));
v___x_497_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34));
v___x_499_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37));
v___x_501_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_Expr_isIte(v_e_472_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = l_Lean_Expr_isDIte(v_e_472_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_505_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_507_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49));
v___x_509_ = l_Lean_Expr_isAppOf(v_e_472_, v___x_508_);
if (v___x_509_ == 0)
{
if (lean_obj_tag(v_e_472_) == 9)
{
lean_object* v_a_510_; 
v_a_510_ = lean_ctor_get(v_e_472_, 0);
if (lean_obj_tag(v_a_510_) == 0)
{
uint8_t v___x_511_; 
lean_dec_ref_known(v_e_472_, 1);
v___x_511_ = 1;
return v___x_511_;
}
else
{
goto v___jp_473_;
}
}
else
{
goto v___jp_473_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_509_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_505_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_503_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_502_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_501_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_499_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_497_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_493_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_491_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_489_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_485_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_483_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___x_481_;
}
}
else
{
lean_dec_ref(v_e_472_);
return v___y_479_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_isInterpretedTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_472_ = stack[0].m_obj;
uint8_t v_res_514_;
v_res_514_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_472_);
stack->m_num = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
return v_x_518_;
}
else
{
lean_object* v_key_520_; lean_object* v_value_521_; lean_object* v_tail_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_545_; 
v_key_520_ = lean_ctor_get(v_x_519_, 0);
v_value_521_ = lean_ctor_get(v_x_519_, 1);
v_tail_522_ = lean_ctor_get(v_x_519_, 2);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_519_);
if (v_isSharedCheck_545_ == 0)
{
v___x_524_ = v_x_519_;
v_isShared_525_ = v_isSharedCheck_545_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_tail_522_);
lean_inc(v_value_521_);
lean_inc(v_key_520_);
lean_dec(v_x_519_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_545_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v_fold_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_526_ = lean_array_get_size(v_x_518_);
v___x_527_ = l_Lean_Expr_hash(v_key_520_);
v___x_528_ = 32ULL;
v___x_529_ = lean_uint64_shift_right(v___x_527_, v___x_528_);
v_fold_530_ = lean_uint64_xor(v___x_527_, v___x_529_);
v___x_531_ = 16ULL;
v___x_532_ = lean_uint64_shift_right(v_fold_530_, v___x_531_);
v___x_533_ = lean_uint64_xor(v_fold_530_, v___x_532_);
v___x_534_ = lean_uint64_to_usize(v___x_533_);
v___x_535_ = lean_usize_of_nat(v___x_526_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_sub(v___x_535_, v___x_536_);
v___x_538_ = lean_usize_land(v___x_534_, v___x_537_);
v___x_539_ = lean_array_uget_borrowed(v_x_518_, v___x_538_);
lean_inc(v___x_539_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 2, v___x_539_);
v___x_541_ = v___x_524_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_key_520_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_value_521_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v___x_539_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_array_uset(v_x_518_, v___x_538_, v___x_541_);
v_x_518_ = v___x_542_;
v_x_519_ = v_tail_522_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_546_, lean_object* v_source_547_, lean_object* v_target_548_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_array_get_size(v_source_547_);
v___x_550_ = lean_nat_dec_lt(v_i_546_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec_ref(v_source_547_);
lean_dec(v_i_546_);
return v_target_548_;
}
else
{
lean_object* v_es_551_; lean_object* v___x_552_; lean_object* v_source_553_; lean_object* v_target_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_es_551_ = lean_array_fget(v_source_547_, v_i_546_);
v___x_552_ = lean_box(0);
v_source_553_ = lean_array_fset(v_source_547_, v_i_546_, v___x_552_);
v_target_554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_548_, v_es_551_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_add(v_i_546_, v___x_555_);
lean_dec(v_i_546_);
v_i_546_ = v___x_556_;
v_source_547_ = v_source_553_;
v_target_548_ = v_target_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_nbuckets_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_559_ = lean_array_get_size(v_data_558_);
v___x_560_ = lean_unsigned_to_nat(2u);
v_nbuckets_561_ = lean_nat_mul(v___x_559_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_box(0);
v___x_564_ = lean_mk_array(v_nbuckets_561_, v___x_563_);
v___x_565_ = lean_array_propagate_mark(v_data_558_, v___x_564_);
v___x_566_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_562_, v_data_558_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_567_, lean_object* v_b_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_dec(v_b_568_);
lean_dec_ref(v_a_567_);
return v_x_569_;
}
else
{
lean_object* v_key_570_; lean_object* v_value_571_; lean_object* v_tail_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_key_570_ = lean_ctor_get(v_x_569_, 0);
v_value_571_ = lean_ctor_get(v_x_569_, 1);
v_tail_572_ = lean_ctor_get(v_x_569_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_x_569_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_tail_572_);
lean_inc(v_value_571_);
lean_inc(v_key_570_);
lean_dec(v_x_569_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
uint8_t v___x_576_; 
v___x_576_ = lean_expr_eqv(v_key_570_, v_a_567_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_567_, v_b_568_, v_tail_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 2, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_key_570_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_value_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
else
{
lean_object* v___x_582_; 
lean_dec(v_value_571_);
lean_dec(v_key_570_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v_b_568_);
lean_ctor_set(v___x_574_, 0, v_a_567_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_567_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_b_568_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_tail_572_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
uint8_t v___x_587_; 
v___x_587_ = 0;
return v___x_587_;
}
else
{
lean_object* v_key_588_; lean_object* v_tail_589_; uint8_t v___x_590_; 
v_key_588_ = lean_ctor_get(v_x_586_, 0);
v_tail_589_ = lean_ctor_get(v_x_586_, 2);
v___x_590_ = lean_expr_eqv(v_key_588_, v_a_585_);
if (v___x_590_ == 0)
{
v_x_586_ = v_tail_589_;
goto _start;
}
else
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_585_ = stack[0].m_obj;
lean_object* v_x_586_ = stack[1].m_obj;
uint8_t v_res_592_;
v_res_592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_585_, v_x_586_);
stack->m_num = v_res_592_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_593_, v_x_594_);
lean_dec(v_x_594_);
lean_dec_ref(v_a_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_size_600_; lean_object* v_buckets_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_644_; 
v_size_600_ = lean_ctor_get(v_m_597_, 0);
v_buckets_601_ = lean_ctor_get(v_m_597_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_m_597_);
if (v_isSharedCheck_644_ == 0)
{
v___x_603_ = v_m_597_;
v_isShared_604_ = v_isSharedCheck_644_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_buckets_601_);
lean_inc(v_size_600_);
lean_dec(v_m_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_644_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v_fold_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v_bkt_618_; uint8_t v___x_619_; 
v___x_605_ = lean_array_get_size(v_buckets_601_);
v___x_606_ = l_Lean_Expr_hash(v_a_598_);
v___x_607_ = 32ULL;
v___x_608_ = lean_uint64_shift_right(v___x_606_, v___x_607_);
v_fold_609_ = lean_uint64_xor(v___x_606_, v___x_608_);
v___x_610_ = 16ULL;
v___x_611_ = lean_uint64_shift_right(v_fold_609_, v___x_610_);
v___x_612_ = lean_uint64_xor(v_fold_609_, v___x_611_);
v___x_613_ = lean_uint64_to_usize(v___x_612_);
v___x_614_ = lean_usize_of_nat(v___x_605_);
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_sub(v___x_614_, v___x_615_);
v___x_617_ = lean_usize_land(v___x_613_, v___x_616_);
v_bkt_618_ = lean_array_uget_borrowed(v_buckets_601_, v___x_617_);
v___x_619_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_598_, v_bkt_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v_size_x27_621_; lean_object* v___x_622_; lean_object* v_buckets_x27_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v_size_x27_621_ = lean_nat_add(v_size_600_, v___x_620_);
lean_dec(v_size_600_);
lean_inc(v_bkt_618_);
v___x_622_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_622_, 0, v_a_598_);
lean_ctor_set(v___x_622_, 1, v_b_599_);
lean_ctor_set(v___x_622_, 2, v_bkt_618_);
v_buckets_x27_623_ = lean_array_uset(v_buckets_601_, v___x_617_, v___x_622_);
v___x_624_ = lean_unsigned_to_nat(4u);
v___x_625_ = lean_nat_mul(v_size_x27_621_, v___x_624_);
v___x_626_ = lean_unsigned_to_nat(3u);
v___x_627_ = lean_nat_div(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_array_get_size(v_buckets_x27_623_);
v___x_629_ = lean_nat_dec_le(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
if (v___x_629_ == 0)
{
lean_object* v_val_630_; lean_object* v___x_632_; 
v_val_630_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_623_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_val_630_);
lean_ctor_set(v___x_603_, 0, v_size_x27_621_);
v___x_632_ = v___x_603_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_size_x27_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_val_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v___x_635_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_buckets_x27_623_);
lean_ctor_set(v___x_603_, 0, v_size_x27_621_);
v___x_635_ = v___x_603_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_size_x27_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_buckets_x27_623_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v___x_637_; lean_object* v_buckets_x27_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_inc(v_bkt_618_);
v___x_637_ = lean_box(0);
v_buckets_x27_638_ = lean_array_uset(v_buckets_601_, v___x_617_, v___x_637_);
v___x_639_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_598_, v_b_599_, v_bkt_618_);
v___x_640_ = lean_array_uset(v_buckets_x27_638_, v___x_617_, v___x_639_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_640_);
v___x_642_ = v___x_603_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_size_600_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_645_, lean_object* v_as_x27_646_, lean_object* v_b_647_){
_start:
{
if (lean_obj_tag(v_as_x27_646_) == 0)
{
lean_dec_ref(v_v_645_);
return v_b_647_;
}
else
{
lean_object* v_head_648_; lean_object* v_tail_649_; lean_object* v___x_650_; 
v_head_648_ = lean_ctor_get(v_as_x27_646_, 0);
v_tail_649_ = lean_ctor_get(v_as_x27_646_, 1);
lean_inc_ref(v_v_645_);
lean_inc(v_head_648_);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_647_, v_head_648_, v_v_645_);
v_as_x27_646_ = v_tail_649_;
v_b_647_ = v___x_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_652_, lean_object* v_as_x27_653_, lean_object* v_b_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_652_, v_as_x27_653_, v_b_654_);
lean_dec(v_as_x27_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_656_, lean_object* v_e_657_, lean_object* v_v_658_, lean_object* v_a_659_){
_start:
{
uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = 0;
v___x_661_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_656_, v_e_657_, v___x_660_);
v___x_662_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_658_, v___x_661_, v_a_659_);
lean_dec(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_663_, lean_object* v_e_664_, lean_object* v_v_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_663_, v_e_664_, v_v_665_, v_a_666_);
lean_dec_ref(v_goal_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_668_, lean_object* v_m_669_, lean_object* v_a_670_, lean_object* v_b_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_669_, v_a_670_, v_b_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_673_, lean_object* v_as_674_, lean_object* v_as_x27_675_, lean_object* v_b_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_673_, v_as_x27_675_, v_b_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_679_, lean_object* v_as_680_, lean_object* v_as_x27_681_, lean_object* v_b_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_679_, v_as_680_, v_as_x27_681_, v_b_682_, v_a_683_);
lean_dec(v_as_x27_681_);
lean_dec(v_as_680_);
return v_res_684_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_685_, lean_object* v_a_686_, lean_object* v_x_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_686_ = stack[1].m_obj;
lean_object* v_x_687_ = stack[2].m_obj;
uint8_t v_res_689_;
v_res_689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_box(0), v_a_686_, v_x_687_);
stack->m_num = v_res_689_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_690_, lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_690_, v_a_691_, v_x_692_);
lean_dec(v_x_692_);
lean_dec_ref(v_a_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_695_, lean_object* v_data_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_698_, lean_object* v_a_699_, lean_object* v_b_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_699_, v_b_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_703_, lean_object* v_i_704_, lean_object* v_source_705_, lean_object* v_target_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_704_, v_source_705_, v_target_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
return v_x_712_;
}
else
{
lean_object* v_key_714_; lean_object* v_value_715_; lean_object* v_tail_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_753_; 
v_key_714_ = lean_ctor_get(v_x_713_, 0);
v_value_715_ = lean_ctor_get(v_x_713_, 1);
v_tail_716_ = lean_ctor_get(v_x_713_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_753_ == 0)
{
v___x_718_ = v_x_713_;
v_isShared_719_ = v_isSharedCheck_753_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_tail_716_);
lean_inc(v_value_715_);
lean_inc(v_key_714_);
lean_dec(v_x_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_753_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint64_t v___y_722_; lean_object* v_intZero_740_; uint8_t v_isNeg_741_; 
v___x_720_ = lean_array_get_size(v_x_712_);
v_intZero_740_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_741_ = lean_int_dec_lt(v_key_714_, v_intZero_740_);
if (v_isNeg_741_ == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint64_t v___x_745_; 
v_a_742_ = lean_nat_abs(v_key_714_);
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_nat_mul(v___x_743_, v_a_742_);
lean_dec(v_a_742_);
v___x_745_ = lean_uint64_of_nat(v___x_744_);
lean_dec(v___x_744_);
v___y_722_ = v___x_745_;
goto v___jp_721_;
}
else
{
lean_object* v_abs_746_; lean_object* v_one_747_; lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint64_t v___x_752_; 
v_abs_746_ = lean_nat_abs(v_key_714_);
v_one_747_ = lean_unsigned_to_nat(1u);
v_a_748_ = lean_nat_sub(v_abs_746_, v_one_747_);
lean_dec(v_abs_746_);
v___x_749_ = lean_unsigned_to_nat(2u);
v___x_750_ = lean_nat_mul(v___x_749_, v_a_748_);
lean_dec(v_a_748_);
v___x_751_ = lean_nat_add(v___x_750_, v_one_747_);
lean_dec(v___x_750_);
v___x_752_ = lean_uint64_of_nat(v___x_751_);
lean_dec(v___x_751_);
v___y_722_ = v___x_752_;
goto v___jp_721_;
}
v___jp_721_:
{
uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v_fold_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_723_ = 32ULL;
v___x_724_ = lean_uint64_shift_right(v___y_722_, v___x_723_);
v_fold_725_ = lean_uint64_xor(v___y_722_, v___x_724_);
v___x_726_ = 16ULL;
v___x_727_ = lean_uint64_shift_right(v_fold_725_, v___x_726_);
v___x_728_ = lean_uint64_xor(v_fold_725_, v___x_727_);
v___x_729_ = lean_uint64_to_usize(v___x_728_);
v___x_730_ = lean_usize_of_nat(v___x_720_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_sub(v___x_730_, v___x_731_);
v___x_733_ = lean_usize_land(v___x_729_, v___x_732_);
v___x_734_ = lean_array_uget_borrowed(v_x_712_, v___x_733_);
lean_inc(v___x_734_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___x_734_);
v___x_736_ = v___x_718_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_key_714_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_value_715_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___x_734_);
v___x_736_ = v_reuseFailAlloc_739_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; 
v___x_737_ = lean_array_uset(v_x_712_, v___x_733_, v___x_736_);
v_x_712_ = v___x_737_;
v_x_713_ = v_tail_716_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_754_, lean_object* v_source_755_, lean_object* v_target_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_source_755_);
v___x_758_ = lean_nat_dec_lt(v_i_754_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec_ref(v_source_755_);
lean_dec(v_i_754_);
return v_target_756_;
}
else
{
lean_object* v_es_759_; lean_object* v___x_760_; lean_object* v_source_761_; lean_object* v_target_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_es_759_ = lean_array_fget(v_source_755_, v_i_754_);
v___x_760_ = lean_box(0);
v_source_761_ = lean_array_fset(v_source_755_, v_i_754_, v___x_760_);
v_target_762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_756_, v_es_759_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_i_754_, v___x_763_);
lean_dec(v_i_754_);
v_i_754_ = v___x_764_;
v_source_755_ = v_source_761_;
v_target_756_ = v_target_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_nbuckets_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_767_ = lean_array_get_size(v_data_766_);
v___x_768_ = lean_unsigned_to_nat(2u);
v_nbuckets_769_ = lean_nat_mul(v___x_767_, v___x_768_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_box(0);
v___x_772_ = lean_mk_array(v_nbuckets_769_, v___x_771_);
v___x_773_ = lean_array_propagate_mark(v_data_766_, v___x_772_);
v___x_774_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_770_, v_data_766_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_775_, lean_object* v_a_776_, lean_object* v_b_777_){
_start:
{
lean_object* v_size_778_; lean_object* v_buckets_779_; lean_object* v___x_780_; uint64_t v___y_782_; lean_object* v_intZero_819_; uint8_t v_isNeg_820_; 
v_size_778_ = lean_ctor_get(v_m_775_, 0);
v_buckets_779_ = lean_ctor_get(v_m_775_, 1);
v___x_780_ = lean_array_get_size(v_buckets_779_);
v_intZero_819_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_820_ = lean_int_dec_lt(v_a_776_, v_intZero_819_);
if (v_isNeg_820_ == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint64_t v___x_824_; 
v_a_821_ = lean_nat_abs(v_a_776_);
v___x_822_ = lean_unsigned_to_nat(2u);
v___x_823_ = lean_nat_mul(v___x_822_, v_a_821_);
lean_dec(v_a_821_);
v___x_824_ = lean_uint64_of_nat(v___x_823_);
lean_dec(v___x_823_);
v___y_782_ = v___x_824_;
goto v___jp_781_;
}
else
{
lean_object* v_abs_825_; lean_object* v_one_826_; lean_object* v_a_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint64_t v___x_831_; 
v_abs_825_ = lean_nat_abs(v_a_776_);
v_one_826_ = lean_unsigned_to_nat(1u);
v_a_827_ = lean_nat_sub(v_abs_825_, v_one_826_);
lean_dec(v_abs_825_);
v___x_828_ = lean_unsigned_to_nat(2u);
v___x_829_ = lean_nat_mul(v___x_828_, v_a_827_);
lean_dec(v_a_827_);
v___x_830_ = lean_nat_add(v___x_829_, v_one_826_);
lean_dec(v___x_829_);
v___x_831_ = lean_uint64_of_nat(v___x_830_);
lean_dec(v___x_830_);
v___y_782_ = v___x_831_;
goto v___jp_781_;
}
v___jp_781_:
{
uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v_fold_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_bkt_794_; uint8_t v___x_795_; 
v___x_783_ = 32ULL;
v___x_784_ = lean_uint64_shift_right(v___y_782_, v___x_783_);
v_fold_785_ = lean_uint64_xor(v___y_782_, v___x_784_);
v___x_786_ = 16ULL;
v___x_787_ = lean_uint64_shift_right(v_fold_785_, v___x_786_);
v___x_788_ = lean_uint64_xor(v_fold_785_, v___x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = lean_usize_of_nat(v___x_780_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_sub(v___x_790_, v___x_791_);
v___x_793_ = lean_usize_land(v___x_789_, v___x_792_);
v_bkt_794_ = lean_array_uget_borrowed(v_buckets_779_, v___x_793_);
v___x_795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_776_, v_bkt_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_816_; 
lean_inc_ref(v_buckets_779_);
lean_inc(v_size_778_);
v_isSharedCheck_816_ = !lean_is_exclusive(v_m_775_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_817_ = lean_ctor_get(v_m_775_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_m_775_, 0);
lean_dec(v_unused_818_);
v___x_797_ = v_m_775_;
v_isShared_798_ = v_isSharedCheck_816_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_m_775_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_816_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v_size_x27_800_; lean_object* v___x_801_; lean_object* v_buckets_x27_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v_size_x27_800_ = lean_nat_add(v_size_778_, v___x_799_);
lean_dec(v_size_778_);
lean_inc(v_bkt_794_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_776_);
lean_ctor_set(v___x_801_, 1, v_b_777_);
lean_ctor_set(v___x_801_, 2, v_bkt_794_);
v_buckets_x27_802_ = lean_array_uset(v_buckets_779_, v___x_793_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(4u);
v___x_804_ = lean_nat_mul(v_size_x27_800_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(3u);
v___x_806_ = lean_nat_div(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_array_get_size(v_buckets_x27_802_);
v___x_808_ = lean_nat_dec_le(v___x_806_, v___x_807_);
lean_dec(v___x_806_);
if (v___x_808_ == 0)
{
lean_object* v_val_809_; lean_object* v___x_811_; 
v_val_809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_802_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_val_809_);
lean_ctor_set(v___x_797_, 0, v_size_x27_800_);
v___x_811_ = v___x_797_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v_buckets_x27_802_);
lean_ctor_set(v___x_797_, 0, v_size_x27_800_);
v___x_814_ = v___x_797_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_buckets_x27_802_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_dec(v_b_777_);
lean_dec(v_a_776_);
return v_m_775_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_832_, lean_object* v_isTarget_833_, lean_object* v_as_834_, size_t v_sz_835_, size_t v_i_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_lt(v_i_836_, v_sz_835_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_isTarget_833_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_837_);
return v___x_844_;
}
else
{
lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_926_; 
v_snd_845_ = lean_ctor_get(v_b_837_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_b_837_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_b_837_, 0);
lean_dec(v_unused_927_);
v___x_847_ = v_b_837_;
v_isShared_848_ = v_isSharedCheck_926_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_dec(v_b_837_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_926_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_925_; 
v_snd_849_ = lean_ctor_get(v_snd_845_, 1);
v_fst_850_ = lean_ctor_get(v_snd_845_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_snd_845_);
if (v_isSharedCheck_925_ == 0)
{
v___x_852_ = v_snd_845_;
v_isShared_853_ = v_isSharedCheck_925_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_850_);
lean_dec(v_snd_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_925_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_924_; 
v_fst_854_ = lean_ctor_get(v_snd_849_, 0);
v_snd_855_ = lean_ctor_get(v_snd_849_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_snd_849_);
if (v_isSharedCheck_924_ == 0)
{
v___x_857_ = v_snd_849_;
v_isShared_858_ = v_isSharedCheck_924_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_snd_855_);
lean_inc(v_fst_854_);
lean_dec(v_snd_849_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_924_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v_a_861_; lean_object* v_a_868_; lean_object* v___x_869_; 
v___x_859_ = lean_box(0);
v_a_868_ = lean_array_uget_borrowed(v_as_834_, v_i_836_);
lean_inc(v_a_868_);
v___x_869_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_832_, v_a_868_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; uint8_t v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_873_; 
lean_dec(v_a_870_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_snd_855_);
lean_ctor_set(v___x_852_, 0, v_fst_854_);
v___x_873_ = v___x_852_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_fst_854_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_snd_855_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_873_);
lean_ctor_set(v___x_847_, 0, v_fst_850_);
v___x_875_ = v___x_847_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_a_861_ = v___x_875_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v___x_878_; 
lean_inc_ref(v_isTarget_833_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v_a_870_);
v___x_878_ = lean_apply_6(v_isTarget_833_, v_a_870_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, lean_box(0));
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_882_; 
lean_dec(v_a_870_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_snd_855_);
lean_ctor_set(v___x_852_, 0, v_fst_854_);
v___x_882_ = v___x_852_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_fst_854_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_snd_855_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_882_);
lean_ctor_set(v___x_847_, 0, v_fst_850_);
v___x_884_ = v___x_847_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v_a_861_ = v___x_884_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v_self_887_; lean_object* v___x_888_; 
v_self_887_ = lean_ctor_get(v_a_870_, 0);
lean_inc_ref(v_self_887_);
lean_dec(v_a_870_);
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_855_, v_self_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_889_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_832_, v_snd_855_, v_self_887_, v_fst_854_, v_fst_850_);
lean_inc_n(v___x_889_, 2);
v___x_890_ = l_Rat_ofInt(v___x_889_);
v___x_891_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_832_, v_self_887_, v___x_890_, v_snd_855_);
v___x_892_ = lean_box(0);
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_854_, v___x_889_, v___x_892_);
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_895_ = lean_int_add(v___x_889_, v___x_894_);
lean_dec(v___x_889_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_891_);
lean_ctor_set(v___x_852_, 0, v___x_893_);
v___x_897_ = v___x_852_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_891_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_897_);
lean_ctor_set(v___x_847_, 0, v___x_895_);
v___x_899_ = v___x_847_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v_a_861_ = v___x_899_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec_ref_known(v___x_888_, 1);
lean_dec_ref(v_self_887_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_snd_855_);
lean_ctor_set(v___x_852_, 0, v_fst_854_);
v___x_903_ = v___x_852_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_fst_854_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_snd_855_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_903_);
lean_ctor_set(v___x_847_, 0, v_fst_850_);
v___x_905_ = v___x_847_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
v_a_861_ = v___x_905_;
goto v___jp_860_;
}
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_a_870_);
lean_del_object(v___x_857_);
lean_dec(v_snd_855_);
lean_dec(v_fst_854_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
lean_del_object(v___x_847_);
lean_dec_ref(v_isTarget_833_);
v_a_908_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_878_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_878_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_del_object(v___x_857_);
lean_dec(v_snd_855_);
lean_dec(v_fst_854_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
lean_del_object(v___x_847_);
lean_dec_ref(v_isTarget_833_);
v_a_916_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_869_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_869_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
v___jp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_a_861_);
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_a_861_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
size_t v___x_864_; size_t v___x_865_; 
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_836_, v___x_864_);
v_i_836_ = v___x_865_;
v_b_837_ = v___x_863_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_832_ = stack[0].m_obj;
lean_object* v_isTarget_833_ = stack[1].m_obj;
lean_object* v_as_834_ = stack[2].m_obj;
size_t v_sz_835_ = stack[3].m_num;
size_t v_i_836_ = stack[4].m_num;
lean_object* v_b_837_ = stack[5].m_obj;
lean_object* v___y_838_ = stack[6].m_obj;
lean_object* v___y_839_ = stack[7].m_obj;
lean_object* v___y_840_ = stack[8].m_obj;
lean_object* v___y_841_ = stack[9].m_obj;
lean_object* v_res_928_;
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_832_, v_isTarget_833_, v_as_834_, v_sz_835_, v_i_836_, v_b_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_929_, lean_object* v_isTarget_930_, lean_object* v_as_931_, lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_941_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_929_, v_isTarget_930_, v_as_931_, v_sz_boxed_940_, v_i_boxed_941_, v_b_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_as_931_);
lean_dec_ref(v_goal_929_);
return v_res_942_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_943_, lean_object* v_isTarget_944_, lean_object* v_as_945_, size_t v_sz_946_, size_t v_i_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_947_, v_sz_946_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v_isTarget_944_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_b_948_);
return v___x_955_;
}
else
{
lean_object* v_snd_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1037_; 
v_snd_956_ = lean_ctor_get(v_b_948_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_b_948_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_b_948_, 0);
lean_dec(v_unused_1038_);
v___x_958_ = v_b_948_;
v_isShared_959_ = v_isSharedCheck_1037_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snd_956_);
lean_dec(v_b_948_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1037_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_snd_960_; lean_object* v_fst_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1036_; 
v_snd_960_ = lean_ctor_get(v_snd_956_, 1);
v_fst_961_ = lean_ctor_get(v_snd_956_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_snd_956_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_963_ = v_snd_956_;
v_isShared_964_ = v_isSharedCheck_1036_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_960_);
lean_inc(v_fst_961_);
lean_dec(v_snd_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1036_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; lean_object* v_snd_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1035_; 
v_fst_965_ = lean_ctor_get(v_snd_960_, 0);
v_snd_966_ = lean_ctor_get(v_snd_960_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_snd_960_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_968_ = v_snd_960_;
v_isShared_969_ = v_isSharedCheck_1035_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snd_966_);
lean_inc(v_fst_965_);
lean_dec(v_snd_960_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1035_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v_a_972_; lean_object* v_a_979_; lean_object* v___x_980_; 
v___x_970_ = lean_box(0);
v_a_979_ = lean_array_uget_borrowed(v_as_945_, v_i_947_);
lean_inc(v_a_979_);
v___x_980_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_943_, v_a_979_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; uint8_t v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_984_; 
lean_dec(v_a_981_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_snd_966_);
lean_ctor_set(v___x_963_, 0, v_fst_965_);
v___x_984_ = v___x_963_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_fst_965_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_snd_966_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_984_);
lean_ctor_set(v___x_958_, 0, v_fst_961_);
v___x_986_ = v___x_958_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
v_a_972_ = v___x_986_;
goto v___jp_971_;
}
}
}
else
{
lean_object* v___x_989_; 
lean_inc_ref(v_isTarget_944_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v_a_981_);
v___x_989_ = lean_apply_6(v_isTarget_944_, v_a_981_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; uint8_t v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v_a_981_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_snd_966_);
lean_ctor_set(v___x_963_, 0, v_fst_965_);
v___x_993_ = v___x_963_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_fst_965_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_snd_966_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_993_);
lean_ctor_set(v___x_958_, 0, v_fst_961_);
v___x_995_ = v___x_958_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
v_a_972_ = v___x_995_;
goto v___jp_971_;
}
}
}
else
{
lean_object* v_self_998_; lean_object* v___x_999_; 
v_self_998_ = lean_ctor_get(v_a_981_, 0);
lean_inc_ref(v_self_998_);
lean_dec(v_a_981_);
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_966_, v_self_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1000_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_943_, v_snd_966_, v_self_998_, v_fst_965_, v_fst_961_);
lean_inc_n(v___x_1000_, 2);
v___x_1001_ = l_Rat_ofInt(v___x_1000_);
v___x_1002_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_943_, v_self_998_, v___x_1001_, v_snd_966_);
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_965_, v___x_1000_, v___x_1003_);
v___x_1005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1006_ = lean_int_add(v___x_1000_, v___x_1005_);
lean_dec(v___x_1000_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___x_1002_);
lean_ctor_set(v___x_963_, 0, v___x_1004_);
v___x_1008_ = v___x_963_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1002_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_1008_);
lean_ctor_set(v___x_958_, 0, v___x_1006_);
v___x_1010_ = v___x_958_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v_a_972_ = v___x_1010_;
goto v___jp_971_;
}
}
}
else
{
lean_object* v___x_1014_; 
lean_dec_ref_known(v___x_999_, 1);
lean_dec_ref(v_self_998_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_snd_966_);
lean_ctor_set(v___x_963_, 0, v_fst_965_);
v___x_1014_ = v___x_963_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_fst_965_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_snd_966_);
v___x_1014_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_1014_);
lean_ctor_set(v___x_958_, 0, v_fst_961_);
v___x_1016_ = v___x_958_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fst_961_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v_a_972_ = v___x_1016_;
goto v___jp_971_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_981_);
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
lean_dec(v_fst_965_);
lean_del_object(v___x_963_);
lean_dec(v_fst_961_);
lean_del_object(v___x_958_);
lean_dec_ref(v_isTarget_944_);
v_a_1019_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_989_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_989_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_968_);
lean_dec(v_snd_966_);
lean_dec(v_fst_965_);
lean_del_object(v___x_963_);
lean_dec(v_fst_961_);
lean_del_object(v___x_958_);
lean_dec_ref(v_isTarget_944_);
v_a_1027_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_980_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_980_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
v___jp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_a_972_);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_974_ = v___x_968_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_a_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_947_, v___x_975_);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_943_, v_isTarget_944_, v_as_945_, v_sz_946_, v___x_976_, v___x_974_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_977_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_943_ = stack[0].m_obj;
lean_object* v_isTarget_944_ = stack[1].m_obj;
lean_object* v_as_945_ = stack[2].m_obj;
size_t v_sz_946_ = stack[3].m_num;
size_t v_i_947_ = stack[4].m_num;
lean_object* v_b_948_ = stack[5].m_obj;
lean_object* v___y_949_ = stack[6].m_obj;
lean_object* v___y_950_ = stack[7].m_obj;
lean_object* v___y_951_ = stack[8].m_obj;
lean_object* v___y_952_ = stack[9].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_943_, v_isTarget_944_, v_as_945_, v_sz_946_, v_i_947_, v_b_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1040_, lean_object* v_isTarget_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
size_t v_sz_boxed_1051_; size_t v_i_boxed_1052_; lean_object* v_res_1053_; 
v_sz_boxed_1051_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1052_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1040_, v_isTarget_1041_, v_as_1042_, v_sz_boxed_1051_, v_i_boxed_1052_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_as_1042_);
lean_dec_ref(v_goal_1040_);
return v_res_1053_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1054_, lean_object* v_isTarget_1055_, lean_object* v_as_1056_, size_t v_sz_1057_, size_t v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
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
lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1148_; 
v_snd_1067_ = lean_ctor_get(v_b_1059_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_b_1059_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_b_1059_, 0);
lean_dec(v_unused_1149_);
v___x_1069_ = v_b_1059_;
v_isShared_1070_ = v_isSharedCheck_1148_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_dec(v_b_1059_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1148_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_snd_1071_; lean_object* v_fst_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1147_; 
v_snd_1071_ = lean_ctor_get(v_snd_1067_, 1);
v_fst_1072_ = lean_ctor_get(v_snd_1067_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_snd_1067_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1074_ = v_snd_1067_;
v_isShared_1075_ = v_isSharedCheck_1147_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_snd_1071_);
lean_inc(v_fst_1072_);
lean_dec(v_snd_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1147_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1146_; 
v_fst_1076_ = lean_ctor_get(v_snd_1071_, 0);
v_snd_1077_ = lean_ctor_get(v_snd_1071_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_snd_1071_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1079_ = v_snd_1071_;
v_isShared_1080_ = v_isSharedCheck_1146_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_inc(v_fst_1076_);
lean_dec(v_snd_1071_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1146_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v_a_1083_; lean_object* v_a_1090_; lean_object* v___x_1091_; 
v___x_1081_ = lean_box(0);
v_a_1090_ = lean_array_uget_borrowed(v_as_1056_, v_i_1058_);
lean_inc(v_a_1090_);
v___x_1091_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1054_, v_a_1090_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; uint8_t v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_a_1092_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_snd_1077_);
lean_ctor_set(v___x_1074_, 0, v_fst_1076_);
v___x_1095_ = v___x_1074_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fst_1076_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_snd_1077_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1095_);
lean_ctor_set(v___x_1069_, 0, v_fst_1072_);
v___x_1097_ = v___x_1069_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fst_1072_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
v_a_1083_ = v___x_1097_;
goto v___jp_1082_;
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
lean_inc(v_a_1092_);
v___x_1100_ = lean_apply_6(v_isTarget_1055_, v_a_1092_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, lean_box(0));
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
lean_dec(v_a_1092_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_snd_1077_);
lean_ctor_set(v___x_1074_, 0, v_fst_1076_);
v___x_1104_ = v___x_1074_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1076_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_snd_1077_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1104_);
lean_ctor_set(v___x_1069_, 0, v_fst_1072_);
v___x_1106_ = v___x_1069_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1072_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v_a_1083_ = v___x_1106_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v_self_1109_; lean_object* v___x_1110_; 
v_self_1109_ = lean_ctor_get(v_a_1092_, 0);
lean_inc_ref(v_self_1109_);
lean_dec(v_a_1092_);
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1077_, v_self_1109_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1111_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1054_, v_snd_1077_, v_self_1109_, v_fst_1076_, v_fst_1072_);
lean_inc_n(v___x_1111_, 2);
v___x_1112_ = l_Rat_ofInt(v___x_1111_);
v___x_1113_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1054_, v_self_1109_, v___x_1112_, v_snd_1077_);
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1076_, v___x_1111_, v___x_1114_);
v___x_1116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1117_ = lean_int_add(v___x_1111_, v___x_1116_);
lean_dec(v___x_1111_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1113_);
lean_ctor_set(v___x_1074_, 0, v___x_1115_);
v___x_1119_ = v___x_1074_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1115_);
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
v_a_1083_ = v___x_1121_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1110_, 1);
lean_dec_ref(v_self_1109_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_snd_1077_);
lean_ctor_set(v___x_1074_, 0, v_fst_1076_);
v___x_1125_ = v___x_1074_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_fst_1076_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_snd_1077_);
v___x_1125_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v___x_1125_);
lean_ctor_set(v___x_1069_, 0, v_fst_1072_);
v___x_1127_ = v___x_1069_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_fst_1072_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v_a_1083_ = v___x_1127_;
goto v___jp_1082_;
}
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_a_1092_);
lean_del_object(v___x_1079_);
lean_dec(v_snd_1077_);
lean_dec(v_fst_1076_);
lean_del_object(v___x_1074_);
lean_dec(v_fst_1072_);
lean_del_object(v___x_1069_);
lean_dec_ref(v_isTarget_1055_);
v_a_1130_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1100_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1100_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_del_object(v___x_1079_);
lean_dec(v_snd_1077_);
lean_dec(v_fst_1076_);
lean_del_object(v___x_1074_);
lean_dec(v_fst_1072_);
lean_del_object(v___x_1069_);
lean_dec_ref(v_isTarget_1055_);
v_a_1138_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1091_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1091_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
v___jp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_a_1083_);
lean_ctor_set(v___x_1079_, 0, v___x_1081_);
v___x_1085_ = v___x_1079_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_a_1083_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1058_, v___x_1086_);
v_i_1058_ = v___x_1087_;
v_b_1059_ = v___x_1085_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1054_ = stack[0].m_obj;
lean_object* v_isTarget_1055_ = stack[1].m_obj;
lean_object* v_as_1056_ = stack[2].m_obj;
size_t v_sz_1057_ = stack[3].m_num;
size_t v_i_1058_ = stack[4].m_num;
lean_object* v_b_1059_ = stack[5].m_obj;
lean_object* v___y_1060_ = stack[6].m_obj;
lean_object* v___y_1061_ = stack[7].m_obj;
lean_object* v___y_1062_ = stack[8].m_obj;
lean_object* v___y_1063_ = stack[9].m_obj;
lean_object* v_res_1150_;
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1054_, v_isTarget_1055_, v_as_1056_, v_sz_1057_, v_i_1058_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
stack->m_obj
 = v_res_1150_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1151_, lean_object* v_isTarget_1152_, lean_object* v_as_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1151_, v_isTarget_1152_, v_as_1153_, v_sz_boxed_1162_, v_i_boxed_1163_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_as_1153_);
lean_dec_ref(v_goal_1151_);
return v_res_1164_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1165_, lean_object* v_isTarget_1166_, lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v_isTarget_1166_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1170_);
return v___x_1177_;
}
else
{
lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1259_; 
v_snd_1178_ = lean_ctor_get(v_b_1170_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_b_1170_, 0);
lean_dec(v_unused_1260_);
v___x_1180_ = v_b_1170_;
v_isShared_1181_ = v_isSharedCheck_1259_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_dec(v_b_1170_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1259_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_snd_1182_; lean_object* v_fst_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1258_; 
v_snd_1182_ = lean_ctor_get(v_snd_1178_, 1);
v_fst_1183_ = lean_ctor_get(v_snd_1178_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_snd_1178_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1185_ = v_snd_1178_;
v_isShared_1186_ = v_isSharedCheck_1258_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1183_);
lean_dec(v_snd_1178_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1258_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1257_; 
v_fst_1187_ = lean_ctor_get(v_snd_1182_, 0);
v_snd_1188_ = lean_ctor_get(v_snd_1182_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_snd_1182_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1190_ = v_snd_1182_;
v_isShared_1191_ = v_isSharedCheck_1257_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_snd_1182_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1257_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_a_1194_; lean_object* v_a_1201_; lean_object* v___x_1202_; 
v___x_1192_ = lean_box(0);
v_a_1201_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
lean_inc(v_a_1201_);
v___x_1202_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1165_, v_a_1201_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; uint8_t v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_a_1203_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_snd_1188_);
lean_ctor_set(v___x_1185_, 0, v_fst_1187_);
v___x_1206_ = v___x_1185_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_snd_1188_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1206_);
lean_ctor_set(v___x_1180_, 0, v_fst_1183_);
v___x_1208_ = v___x_1180_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v_a_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v___x_1211_; 
lean_inc_ref(v_isTarget_1166_);
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1173_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v_a_1203_);
v___x_1211_ = lean_apply_6(v_isTarget_1166_, v_a_1203_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, lean_box(0));
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; uint8_t v___x_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = lean_unbox(v_a_1212_);
lean_dec(v_a_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_a_1203_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_snd_1188_);
lean_ctor_set(v___x_1185_, 0, v_fst_1187_);
v___x_1215_ = v___x_1185_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1188_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1215_);
lean_ctor_set(v___x_1180_, 0, v_fst_1183_);
v___x_1217_ = v___x_1180_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
v_a_1194_ = v___x_1217_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v_self_1220_; lean_object* v___x_1221_; 
v_self_1220_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_ref(v_self_1220_);
lean_dec(v_a_1203_);
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1188_, v_self_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1222_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1165_, v_snd_1188_, v_self_1220_, v_fst_1187_, v_fst_1183_);
lean_inc_n(v___x_1222_, 2);
v___x_1223_ = l_Rat_ofInt(v___x_1222_);
v___x_1224_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1165_, v_self_1220_, v___x_1223_, v_snd_1188_);
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1187_, v___x_1222_, v___x_1225_);
v___x_1227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1228_ = lean_int_add(v___x_1222_, v___x_1227_);
lean_dec(v___x_1222_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1224_);
lean_ctor_set(v___x_1185_, 0, v___x_1226_);
v___x_1230_ = v___x_1185_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1224_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1230_);
lean_ctor_set(v___x_1180_, 0, v___x_1228_);
v___x_1232_ = v___x_1180_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
v_a_1194_ = v___x_1232_;
goto v___jp_1193_;
}
}
}
else
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1221_, 1);
lean_dec_ref(v_self_1220_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_snd_1188_);
lean_ctor_set(v___x_1185_, 0, v_fst_1187_);
v___x_1236_ = v___x_1185_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1188_);
v___x_1236_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1238_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1236_);
lean_ctor_set(v___x_1180_, 0, v_fst_1183_);
v___x_1238_ = v___x_1180_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v_a_1194_ = v___x_1238_;
goto v___jp_1193_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_a_1203_);
lean_del_object(v___x_1190_);
lean_dec(v_snd_1188_);
lean_dec(v_fst_1187_);
lean_del_object(v___x_1185_);
lean_dec(v_fst_1183_);
lean_del_object(v___x_1180_);
lean_dec_ref(v_isTarget_1166_);
v_a_1241_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1211_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1211_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_del_object(v___x_1190_);
lean_dec(v_snd_1188_);
lean_dec(v_fst_1187_);
lean_del_object(v___x_1185_);
lean_dec(v_fst_1183_);
lean_del_object(v___x_1180_);
lean_dec_ref(v_isTarget_1166_);
v_a_1249_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1202_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1202_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
v___jp_1193_:
{
lean_object* v___x_1196_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_a_1194_);
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1196_ = v___x_1190_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_a_1194_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_add(v_i_1169_, v___x_1197_);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1165_, v_isTarget_1166_, v_as_1167_, v_sz_1168_, v___x_1198_, v___x_1196_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1199_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1165_ = stack[0].m_obj;
lean_object* v_isTarget_1166_ = stack[1].m_obj;
lean_object* v_as_1167_ = stack[2].m_obj;
size_t v_sz_1168_ = stack[3].m_num;
size_t v_i_1169_ = stack[4].m_num;
lean_object* v_b_1170_ = stack[5].m_obj;
lean_object* v___y_1171_ = stack[6].m_obj;
lean_object* v___y_1172_ = stack[7].m_obj;
lean_object* v___y_1173_ = stack[8].m_obj;
lean_object* v___y_1174_ = stack[9].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1165_, v_isTarget_1166_, v_as_1167_, v_sz_1168_, v_i_1169_, v_b_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1262_, lean_object* v_isTarget_1263_, lean_object* v_as_1264_, lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1262_, v_isTarget_1263_, v_as_1264_, v_sz_boxed_1273_, v_i_boxed_1274_, v_b_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v_as_1264_);
lean_dec_ref(v_goal_1262_);
return v_res_1275_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1276_, lean_object* v_goal_1277_, lean_object* v_isTarget_1278_, lean_object* v_n_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
if (lean_obj_tag(v_n_1279_) == 0)
{
lean_object* v_cs_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; size_t v_sz_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v_cs_1286_ = lean_ctor_get(v_n_1279_, 0);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_b_1280_);
v_sz_1289_ = lean_array_size(v_cs_1286_);
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1276_, v_goal_1277_, v_isTarget_1278_, v_cs_1286_, v_sz_1289_, v___x_1290_, v___x_1288_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1306_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_fst_1296_; 
v_fst_1296_ = lean_ctor_get(v_a_1292_, 0);
if (lean_obj_tag(v_fst_1296_) == 0)
{
lean_object* v_snd_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v_snd_1297_ = lean_ctor_get(v_a_1292_, 1);
lean_inc(v_snd_1297_);
lean_dec(v_a_1292_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_snd_1297_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
lean_inc_ref(v_fst_1296_);
lean_dec(v_a_1292_);
v_val_1302_ = lean_ctor_get(v_fst_1296_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v_fst_1296_, 1);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_val_1302_);
v___x_1304_ = v___x_1294_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1291_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1291_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_vs_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; size_t v_sz_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v_vs_1315_ = lean_ctor_get(v_n_1279_, 0);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_b_1280_);
v_sz_1318_ = lean_array_size(v_vs_1315_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1277_, v_isTarget_1278_, v_vs_1315_, v_sz_1318_, v___x_1319_, v___x_1317_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1335_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_fst_1325_; 
v_fst_1325_ = lean_ctor_get(v_a_1321_, 0);
if (lean_obj_tag(v_fst_1325_) == 0)
{
lean_object* v_snd_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v_snd_1326_ = lean_ctor_get(v_a_1321_, 1);
lean_inc(v_snd_1326_);
lean_dec(v_a_1321_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_snd_1326_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; 
lean_inc_ref(v_fst_1325_);
lean_dec(v_a_1321_);
v_val_1331_ = lean_ctor_get(v_fst_1325_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_fst_1325_, 1);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_val_1331_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_val_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1320_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1320_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1276_ = stack[0].m_obj;
lean_object* v_goal_1277_ = stack[1].m_obj;
lean_object* v_isTarget_1278_ = stack[2].m_obj;
lean_object* v_n_1279_ = stack[3].m_obj;
lean_object* v_b_1280_ = stack[4].m_obj;
lean_object* v___y_1281_ = stack[5].m_obj;
lean_object* v___y_1282_ = stack[6].m_obj;
lean_object* v___y_1283_ = stack[7].m_obj;
lean_object* v___y_1284_ = stack[8].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1276_, v_goal_1277_, v_isTarget_1278_, v_n_1279_, v_b_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
stack->m_obj
 = v_res_1344_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1345_, lean_object* v_goal_1346_, lean_object* v_isTarget_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref(v_isTarget_1347_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1351_);
return v___x_1358_;
}
else
{
lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1393_; 
v_snd_1359_ = lean_ctor_get(v_b_1351_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v_b_1351_, 0);
lean_dec(v_unused_1394_);
v___x_1361_ = v_b_1351_;
v_isShared_1362_ = v_isSharedCheck_1393_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_dec(v_b_1351_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1393_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v_a_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_box(0);
v_a_1364_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
lean_inc(v_snd_1359_);
lean_inc_ref(v_isTarget_1347_);
v___x_1365_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1345_, v_goal_1346_, v_isTarget_1347_, v_a_1364_, v_snd_1359_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1384_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1384_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
if (lean_obj_tag(v_a_1366_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec_ref(v_isTarget_1347_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1366_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1370_);
v___x_1372_ = v___x_1361_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1359_);
v___x_1372_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1374_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1372_);
v___x_1374_ = v___x_1368_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; 
lean_del_object(v___x_1368_);
lean_dec(v_snd_1359_);
v_a_1377_ = lean_ctor_get(v_a_1366_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v_a_1366_, 1);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v_a_1377_);
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1379_ = v___x_1361_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_a_1377_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
size_t v___x_1380_; size_t v___x_1381_; 
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1350_, v___x_1380_);
v_i_1350_ = v___x_1381_;
v_b_1351_ = v___x_1379_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_del_object(v___x_1361_);
lean_dec(v_snd_1359_);
lean_dec_ref(v_isTarget_1347_);
v_a_1385_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1365_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1365_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1345_ = stack[0].m_obj;
lean_object* v_goal_1346_ = stack[1].m_obj;
lean_object* v_isTarget_1347_ = stack[2].m_obj;
lean_object* v_as_1348_ = stack[3].m_obj;
size_t v_sz_1349_ = stack[4].m_num;
size_t v_i_1350_ = stack[5].m_num;
lean_object* v_b_1351_ = stack[6].m_obj;
lean_object* v___y_1352_ = stack[7].m_obj;
lean_object* v___y_1353_ = stack[8].m_obj;
lean_object* v___y_1354_ = stack[9].m_obj;
lean_object* v___y_1355_ = stack[10].m_obj;
lean_object* v_res_1395_;
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1345_, v_goal_1346_, v_isTarget_1347_, v_as_1348_, v_sz_1349_, v_i_1350_, v_b_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
stack->m_obj
 = v_res_1395_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1396_, lean_object* v_goal_1397_, lean_object* v_isTarget_1398_, lean_object* v_as_1399_, lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
size_t v_sz_boxed_1408_; size_t v_i_boxed_1409_; lean_object* v_res_1410_; 
v_sz_boxed_1408_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1409_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1396_, v_goal_1397_, v_isTarget_1398_, v_as_1399_, v_sz_boxed_1408_, v_i_boxed_1409_, v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_as_1399_);
lean_dec_ref(v_goal_1397_);
lean_dec_ref(v_init_1396_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1411_, lean_object* v_goal_1412_, lean_object* v_isTarget_1413_, lean_object* v_n_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1411_, v_goal_1412_, v_isTarget_1413_, v_n_1414_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_n_1414_);
lean_dec_ref(v_goal_1412_);
lean_dec_ref(v_init_1411_);
return v_res_1421_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1422_, lean_object* v_isTarget_1423_, lean_object* v_t_1424_, lean_object* v_init_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_root_1431_; lean_object* v_tail_1432_; lean_object* v___x_1433_; 
v_root_1431_ = lean_ctor_get(v_t_1424_, 0);
v_tail_1432_ = lean_ctor_get(v_t_1424_, 1);
lean_inc_ref(v_isTarget_1423_);
lean_inc_ref(v_init_1425_);
v___x_1433_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1425_, v_goal_1422_, v_isTarget_1423_, v_root_1431_, v_init_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec_ref(v_init_1425_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1470_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1470_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1470_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
if (lean_obj_tag(v_a_1434_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; 
lean_dec_ref(v_isTarget_1423_);
v_a_1438_ = lean_ctor_get(v_a_1434_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v_a_1434_, 1);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_a_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; size_t v_sz_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
lean_del_object(v___x_1436_);
v_a_1442_ = lean_ctor_get(v_a_1434_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v_a_1434_, 1);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v_a_1442_);
v_sz_1445_ = lean_array_size(v_tail_1432_);
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1422_, v_isTarget_1423_, v_tail_1432_, v_sz_1445_, v___x_1446_, v___x_1444_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1461_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1461_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1461_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_fst_1452_; 
v_fst_1452_ = lean_ctor_get(v_a_1448_, 0);
if (lean_obj_tag(v_fst_1452_) == 0)
{
lean_object* v_snd_1453_; lean_object* v___x_1455_; 
v_snd_1453_ = lean_ctor_get(v_a_1448_, 1);
lean_inc(v_snd_1453_);
lean_dec(v_a_1448_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v_snd_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_snd_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1459_; 
lean_inc_ref(v_fst_1452_);
lean_dec(v_a_1448_);
v_val_1457_ = lean_ctor_get(v_fst_1452_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v_fst_1452_, 1);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v_val_1457_);
v___x_1459_ = v___x_1450_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_val_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1447_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1447_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v_isTarget_1423_);
v_a_1471_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1433_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1433_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1422_ = stack[0].m_obj;
lean_object* v_isTarget_1423_ = stack[1].m_obj;
lean_object* v_t_1424_ = stack[2].m_obj;
lean_object* v_init_1425_ = stack[3].m_obj;
lean_object* v___y_1426_ = stack[4].m_obj;
lean_object* v___y_1427_ = stack[5].m_obj;
lean_object* v___y_1428_ = stack[6].m_obj;
lean_object* v___y_1429_ = stack[7].m_obj;
lean_object* v_res_1479_;
v_res_1479_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1422_, v_isTarget_1423_, v_t_1424_, v_init_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
stack->m_obj
 = v_res_1479_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1480_, lean_object* v_isTarget_1481_, lean_object* v_t_1482_, lean_object* v_init_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1480_, v_isTarget_1481_, v_t_1482_, v_init_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v_t_1482_);
lean_dec_ref(v_goal_1480_);
return v_res_1489_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
if (lean_obj_tag(v_a_1490_) == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_a_1491_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
else
{
lean_object* v_value_1495_; lean_object* v_tail_1496_; lean_object* v_num_1497_; lean_object* v_den_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_value_1495_ = lean_ctor_get(v_a_1490_, 1);
lean_inc(v_value_1495_);
v_tail_1496_ = lean_ctor_get(v_a_1490_, 2);
lean_inc(v_tail_1496_);
lean_dec_ref_known(v_a_1490_, 3);
v_num_1497_ = lean_ctor_get(v_value_1495_, 0);
lean_inc(v_num_1497_);
v_den_1498_ = lean_ctor_get(v_value_1495_, 1);
lean_inc(v_den_1498_);
lean_dec(v_value_1495_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_dec_eq(v_den_1498_, v___x_1499_);
lean_dec(v_den_1498_);
if (v___x_1500_ == 0)
{
lean_dec(v_num_1497_);
v_a_1490_ = v_tail_1496_;
goto _start;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1491_, v_num_1497_, v___x_1502_);
v_a_1490_ = v_tail_1496_;
v_a_1491_ = v___x_1503_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1490_ = stack[0].m_obj;
lean_object* v_a_1491_ = stack[1].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1490_, v_a_1491_);
stack->m_obj
 = v_res_1505_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1506_, v_a_1507_);
return v_res_1509_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1510_, size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_b_1513_);
return v___x_1520_;
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1521_ = lean_array_uget_borrowed(v_as_1510_, v_i_1512_);
lean_inc(v_a_1521_);
v___x_1522_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1521_, v_b_1513_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1535_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
if (lean_obj_tag(v_a_1523_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; 
v_a_1527_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v_a_1523_, 1);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_a_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
else
{
lean_object* v_a_1531_; size_t v___x_1532_; size_t v___x_1533_; 
lean_del_object(v___x_1525_);
v_a_1531_ = lean_ctor_get(v_a_1523_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v_a_1523_, 1);
v___x_1532_ = ((size_t)1ULL);
v___x_1533_ = lean_usize_add(v_i_1512_, v___x_1532_);
v_i_1512_ = v___x_1533_;
v_b_1513_ = v_a_1531_;
goto _start;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1522_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1522_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1510_ = stack[0].m_obj;
size_t v_sz_1511_ = stack[1].m_num;
size_t v_i_1512_ = stack[2].m_num;
lean_object* v_b_1513_ = stack[3].m_obj;
lean_object* v___y_1514_ = stack[4].m_obj;
lean_object* v___y_1515_ = stack[5].m_obj;
lean_object* v___y_1516_ = stack[6].m_obj;
lean_object* v___y_1517_ = stack[7].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1510_, v_sz_1511_, v_i_1512_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
size_t v_sz_boxed_1554_; size_t v_i_boxed_1555_; lean_object* v_res_1556_; 
v_sz_boxed_1554_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1555_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1545_, v_sz_boxed_1554_, v_i_boxed_1555_, v_b_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_as_1545_);
return v_res_1556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_unsigned_to_nat(16u);
v___x_1559_ = lean_mk_array(v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_used_1562_; 
v___x_1560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1561_ = lean_unsigned_to_nat(0u);
v_used_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1562_, 0, v___x_1561_);
lean_ctor_set(v_used_1562_, 1, v___x_1560_);
return v_used_1562_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1563_, lean_object* v_isTarget_1564_, lean_object* v_model_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_buckets_1571_; lean_object* v_nextVal_1572_; lean_object* v_used_1573_; size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v_buckets_1571_ = lean_ctor_get(v_model_1565_, 1);
v_nextVal_1572_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_used_1573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1574_ = lean_array_size(v_buckets_1571_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1571_, v_sz_1574_, v___x_1575_, v_used_1573_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_toGoalState_1577_; lean_object* v_a_1578_; lean_object* v_exprs_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_toGoalState_1577_ = lean_ctor_get(v_goal_1563_, 0);
v_a_1578_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1576_, 1);
v_exprs_1579_ = lean_ctor_get(v_toGoalState_1577_, 2);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1578_);
lean_ctor_set(v___x_1580_, 1, v_model_1565_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_nextVal_1572_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1563_, v_isTarget_1564_, v_exprs_1579_, v___x_1581_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1592_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_snd_1587_; lean_object* v_snd_1588_; lean_object* v___x_1590_; 
v_snd_1587_ = lean_ctor_get(v_a_1583_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_a_1583_);
v_snd_1588_ = lean_ctor_get(v_snd_1587_, 1);
lean_inc(v_snd_1588_);
lean_dec(v_snd_1587_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v_snd_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_snd_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1582_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1582_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_model_1565_);
lean_dec_ref(v_isTarget_1564_);
v_a_1601_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1576_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1576_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1563_ = stack[0].m_obj;
lean_object* v_isTarget_1564_ = stack[1].m_obj;
lean_object* v_model_1565_ = stack[2].m_obj;
lean_object* v_a_1566_ = stack[3].m_obj;
lean_object* v_a_1567_ = stack[4].m_obj;
lean_object* v_a_1568_ = stack[5].m_obj;
lean_object* v_a_1569_ = stack[6].m_obj;
lean_object* v_res_1609_;
v_res_1609_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1563_, v_isTarget_1564_, v_model_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
stack->m_obj
 = v_res_1609_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1610_, lean_object* v_isTarget_1611_, lean_object* v_model_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1610_, v_isTarget_1611_, v_model_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec_ref(v_goal_1610_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1619_, lean_object* v_m_1620_, lean_object* v_a_1621_, lean_object* v_b_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1620_, v_a_1621_, v_b_1622_);
return v___x_1623_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1624_, v_a_1625_);
return v___x_1631_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1624_ = stack[0].m_obj;
lean_object* v_a_1625_ = stack[1].m_obj;
lean_object* v___y_1626_ = stack[2].m_obj;
lean_object* v___y_1627_ = stack[3].m_obj;
lean_object* v___y_1628_ = stack[4].m_obj;
lean_object* v___y_1629_ = stack[5].m_obj;
lean_object* v_res_1632_;
v_res_1632_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1624_, v_a_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
stack->m_obj
 = v_res_1632_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1633_, v_a_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1641_, lean_object* v_data_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1644_, lean_object* v_i_1645_, lean_object* v_source_1646_, lean_object* v_target_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1645_, v_source_1646_, v_target_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1650_, v_x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1653_, lean_object* v_hi_1654_, lean_object* v_pivot_1655_, lean_object* v_as_1656_, lean_object* v_i_1657_, lean_object* v_k_1658_){
_start:
{
uint8_t v___y_1660_; uint8_t v___x_1669_; 
v___x_1669_ = lean_nat_dec_lt(v_k_1658_, v_hi_1654_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v_k_1658_);
v___x_1670_ = lean_array_fswap(v_as_1656_, v_i_1657_, v_hi_1654_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_i_1657_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; lean_object* v_fst_1673_; lean_object* v_fst_1674_; lean_object* v_g_u2081_1675_; lean_object* v_g_u2082_1676_; uint8_t v___x_1677_; 
v___x_1672_ = lean_array_fget_borrowed(v_as_1656_, v_k_1658_);
v_fst_1673_ = lean_ctor_get(v___x_1672_, 0);
v_fst_1674_ = lean_ctor_get(v_pivot_1655_, 0);
v_g_u2081_1675_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1653_, v_fst_1673_);
v_g_u2082_1676_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1653_, v_fst_1674_);
v___x_1677_ = lean_nat_dec_eq(v_g_u2081_1675_, v_g_u2082_1676_);
if (v___x_1677_ == 0)
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_nat_dec_lt(v_g_u2081_1675_, v_g_u2082_1676_);
lean_dec(v_g_u2082_1676_);
lean_dec(v_g_u2081_1675_);
v___y_1660_ = v___x_1678_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1679_; 
lean_dec(v_g_u2082_1676_);
lean_dec(v_g_u2081_1675_);
v___x_1679_ = lean_expr_lt(v_fst_1673_, v_fst_1674_);
v___y_1660_ = v___x_1679_;
goto v___jp_1659_;
}
}
v___jp_1659_:
{
if (v___y_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_nat_add(v_k_1658_, v___x_1661_);
lean_dec(v_k_1658_);
v_k_1658_ = v___x_1662_;
goto _start;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = lean_array_fswap(v_as_1656_, v_i_1657_, v_k_1658_);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_i_1657_, v___x_1665_);
lean_dec(v_i_1657_);
v___x_1667_ = lean_nat_add(v_k_1658_, v___x_1665_);
lean_dec(v_k_1658_);
v_as_1656_ = v___x_1664_;
v_i_1657_ = v___x_1666_;
v_k_1658_ = v___x_1667_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1680_, lean_object* v_hi_1681_, lean_object* v_pivot_1682_, lean_object* v_as_1683_, lean_object* v_i_1684_, lean_object* v_k_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1680_, v_hi_1681_, v_pivot_1682_, v_as_1683_, v_i_1684_, v_k_1685_);
lean_dec_ref(v_pivot_1682_);
lean_dec(v_hi_1681_);
lean_dec_ref(v_goal_1680_);
return v_res_1686_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
lean_object* v_fst_1690_; lean_object* v_fst_1691_; lean_object* v_g_u2081_1692_; lean_object* v_g_u2082_1693_; uint8_t v___x_1694_; 
v_fst_1690_ = lean_ctor_get(v_x_1688_, 0);
v_fst_1691_ = lean_ctor_get(v_x_1689_, 0);
v_g_u2081_1692_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1687_, v_fst_1690_);
v_g_u2082_1693_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1687_, v_fst_1691_);
v___x_1694_ = lean_nat_dec_eq(v_g_u2081_1692_, v_g_u2082_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_nat_dec_lt(v_g_u2081_1692_, v_g_u2082_1693_);
lean_dec(v_g_u2082_1693_);
lean_dec(v_g_u2081_1692_);
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; 
lean_dec(v_g_u2082_1693_);
lean_dec(v_g_u2081_1692_);
v___x_1696_ = lean_expr_lt(v_fst_1690_, v_fst_1691_);
return v___x_1696_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1687_ = stack[0].m_obj;
lean_object* v_x_1688_ = stack[1].m_obj;
lean_object* v_x_1689_ = stack[2].m_obj;
uint8_t v_res_1697_;
v_res_1697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1687_, v_x_1688_, v_x_1689_);
stack->m_num = v_res_1697_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
uint8_t v_res_1701_; lean_object* v_r_1702_; 
v_res_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1698_, v_x_1699_, v_x_1700_);
lean_dec_ref(v_x_1700_);
lean_dec_ref(v_x_1699_);
lean_dec_ref(v_goal_1698_);
v_r_1702_ = lean_box(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1703_, lean_object* v_n_1704_, lean_object* v_as_1705_, lean_object* v_lo_1706_, lean_object* v_hi_1707_){
_start:
{
lean_object* v___y_1709_; uint8_t v___x_1719_; 
v___x_1719_ = lean_nat_dec_lt(v_lo_1706_, v_hi_1707_);
if (v___x_1719_ == 0)
{
lean_dec(v_lo_1706_);
return v_as_1705_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v_mid_1722_; lean_object* v___y_1724_; lean_object* v___y_1730_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1720_ = lean_nat_add(v_lo_1706_, v_hi_1707_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v_mid_1722_ = lean_nat_shiftr(v___x_1720_, v___x_1721_);
lean_dec(v___x_1720_);
v___x_1735_ = lean_array_fget_borrowed(v_as_1705_, v_mid_1722_);
v___x_1736_ = lean_array_fget_borrowed(v_as_1705_, v_lo_1706_);
v___x_1737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1703_, v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
v___y_1730_ = v_as_1705_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_array_fswap(v_as_1705_, v_lo_1706_, v_mid_1722_);
v___y_1730_ = v___x_1738_;
goto v___jp_1729_;
}
v___jp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_array_fget_borrowed(v___y_1724_, v_mid_1722_);
v___x_1726_ = lean_array_fget_borrowed(v___y_1724_, v_hi_1707_);
v___x_1727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1703_, v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v_mid_1722_);
v___y_1709_ = v___y_1724_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_array_fswap(v___y_1724_, v_mid_1722_, v_hi_1707_);
lean_dec(v_mid_1722_);
v___y_1709_ = v___x_1728_;
goto v___jp_1708_;
}
}
v___jp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1731_ = lean_array_fget_borrowed(v___y_1730_, v_hi_1707_);
v___x_1732_ = lean_array_fget_borrowed(v___y_1730_, v_lo_1706_);
v___x_1733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1703_, v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
v___y_1724_ = v___y_1730_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_array_fswap(v___y_1730_, v_lo_1706_, v_hi_1707_);
v___y_1724_ = v___x_1734_;
goto v___jp_1723_;
}
}
}
v___jp_1708_:
{
lean_object* v_pivot_1710_; lean_object* v___x_1711_; lean_object* v_fst_1712_; lean_object* v_snd_1713_; uint8_t v___x_1714_; 
v_pivot_1710_ = lean_array_fget(v___y_1709_, v_hi_1707_);
lean_inc_n(v_lo_1706_, 2);
v___x_1711_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1703_, v_hi_1707_, v_pivot_1710_, v___y_1709_, v_lo_1706_, v_lo_1706_);
lean_dec(v_pivot_1710_);
v_fst_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_fst_1712_);
v_snd_1713_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_snd_1713_);
lean_dec_ref(v___x_1711_);
v___x_1714_ = lean_nat_dec_le(v_hi_1707_, v_fst_1712_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1703_, v_n_1704_, v_snd_1713_, v_lo_1706_, v_fst_1712_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_fst_1712_, v___x_1716_);
lean_dec(v_fst_1712_);
v_as_1705_ = v___x_1715_;
v_lo_1706_ = v___x_1717_;
goto _start;
}
else
{
lean_dec(v_fst_1712_);
lean_dec(v_lo_1706_);
return v_snd_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1739_, lean_object* v_n_1740_, lean_object* v_as_1741_, lean_object* v_lo_1742_, lean_object* v_hi_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1739_, v_n_1740_, v_as_1741_, v_lo_1742_, v_hi_1743_);
lean_dec(v_hi_1743_);
lean_dec(v_n_1740_);
lean_dec_ref(v_goal_1739_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1745_, lean_object* v_m_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = lean_array_get_size(v_m_1746_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_nat_dec_eq(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___y_1753_; uint8_t v___x_1757_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_sub(v___x_1747_, v___x_1750_);
v___x_1757_ = lean_nat_dec_le(v___x_1748_, v___x_1751_);
if (v___x_1757_ == 0)
{
lean_inc(v___x_1751_);
v___y_1753_ = v___x_1751_;
goto v___jp_1752_;
}
else
{
v___y_1753_ = v___x_1748_;
goto v___jp_1752_;
}
v___jp_1752_:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_nat_dec_le(v___y_1753_, v___x_1751_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec(v___x_1751_);
lean_inc(v___y_1753_);
v___x_1755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1745_, v___x_1747_, v_m_1746_, v___y_1753_, v___y_1753_);
lean_dec(v___y_1753_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1745_, v___x_1747_, v_m_1746_, v___y_1753_, v___x_1751_);
lean_dec(v___x_1751_);
return v___x_1756_;
}
}
}
else
{
return v_m_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1758_, lean_object* v_m_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1758_, v_m_1759_);
lean_dec_ref(v_goal_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1761_, lean_object* v_n_1762_, lean_object* v_as_1763_, lean_object* v_lo_1764_, lean_object* v_hi_1765_, lean_object* v_w_1766_, lean_object* v_hlo_1767_, lean_object* v_hhi_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1761_, v_n_1762_, v_as_1763_, v_lo_1764_, v_hi_1765_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1770_, lean_object* v_n_1771_, lean_object* v_as_1772_, lean_object* v_lo_1773_, lean_object* v_hi_1774_, lean_object* v_w_1775_, lean_object* v_hlo_1776_, lean_object* v_hhi_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1770_, v_n_1771_, v_as_1772_, v_lo_1773_, v_hi_1774_, v_w_1775_, v_hlo_1776_, v_hhi_1777_);
lean_dec(v_hi_1774_);
lean_dec(v_n_1771_);
lean_dec_ref(v_goal_1770_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1779_, lean_object* v_n_1780_, lean_object* v_lo_1781_, lean_object* v_hi_1782_, lean_object* v_hhi_1783_, lean_object* v_pivot_1784_, lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_k_1787_, lean_object* v_ilo_1788_, lean_object* v_ik_1789_, lean_object* v_w_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1779_, v_hi_1782_, v_pivot_1784_, v_as_1785_, v_i_1786_, v_k_1787_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1792_, lean_object* v_n_1793_, lean_object* v_lo_1794_, lean_object* v_hi_1795_, lean_object* v_hhi_1796_, lean_object* v_pivot_1797_, lean_object* v_as_1798_, lean_object* v_i_1799_, lean_object* v_k_1800_, lean_object* v_ilo_1801_, lean_object* v_ik_1802_, lean_object* v_w_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1792_, v_n_1793_, v_lo_1794_, v_hi_1795_, v_hhi_1796_, v_pivot_1797_, v_as_1798_, v_i_1799_, v_k_1800_, v_ilo_1801_, v_ik_1802_, v_w_1803_);
lean_dec_ref(v_pivot_1797_);
lean_dec(v_hi_1795_);
lean_dec(v_lo_1794_);
lean_dec(v_n_1793_);
lean_dec_ref(v_goal_1792_);
return v_res_1804_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
if (lean_obj_tag(v_a_1805_) == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1806_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
else
{
lean_object* v_key_1810_; lean_object* v_value_1811_; lean_object* v_tail_1812_; uint8_t v___x_1813_; 
v_key_1810_ = lean_ctor_get(v_a_1805_, 0);
lean_inc_n(v_key_1810_, 2);
v_value_1811_ = lean_ctor_get(v_a_1805_, 1);
lean_inc(v_value_1811_);
v_tail_1812_ = lean_ctor_get(v_a_1805_, 2);
lean_inc(v_tail_1812_);
lean_dec_ref_known(v_a_1805_, 3);
v___x_1813_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1810_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_key_1810_);
lean_ctor_set(v___x_1814_, 1, v_value_1811_);
v___x_1815_ = lean_array_push(v_a_1806_, v___x_1814_);
v_a_1805_ = v_tail_1812_;
v_a_1806_ = v___x_1815_;
goto _start;
}
else
{
lean_dec(v_value_1811_);
lean_dec(v_key_1810_);
v_a_1805_ = v_tail_1812_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1805_ = stack[0].m_obj;
lean_object* v_a_1806_ = stack[1].m_obj;
lean_object* v_res_1818_;
v_res_1818_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1805_, v_a_1806_);
stack->m_obj
 = v_res_1818_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1819_, v_a_1820_);
return v_res_1822_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1823_, size_t v_sz_1824_, size_t v_i_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_usize_dec_lt(v_i_1825_, v_sz_1824_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_b_1826_);
return v___x_1833_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_array_uget_borrowed(v_as_1823_, v_i_1825_);
lean_inc(v_a_1834_);
v___x_1835_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1834_, v_b_1826_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1848_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v_a_1836_, 1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_a_1844_; size_t v___x_1845_; size_t v___x_1846_; 
lean_del_object(v___x_1838_);
v_a_1844_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v_a_1836_, 1);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1825_, v___x_1845_);
v_i_1825_ = v___x_1846_;
v_b_1826_ = v_a_1844_;
goto _start;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1835_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1823_ = stack[0].m_obj;
size_t v_sz_1824_ = stack[1].m_num;
size_t v_i_1825_ = stack[2].m_num;
lean_object* v_b_1826_ = stack[3].m_obj;
lean_object* v___y_1827_ = stack[4].m_obj;
lean_object* v___y_1828_ = stack[5].m_obj;
lean_object* v___y_1829_ = stack[6].m_obj;
lean_object* v___y_1830_ = stack[7].m_obj;
lean_object* v_res_1857_;
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1823_, v_sz_1824_, v_i_1825_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
stack->m_obj
 = v_res_1857_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1858_, lean_object* v_sz_1859_, lean_object* v_i_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1859_);
lean_dec(v_sz_1859_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1858_, v_sz_boxed_1867_, v_i_boxed_1868_, v_b_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_as_1858_);
return v_res_1869_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1872_, lean_object* v_isTarget_1873_, lean_object* v_model_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1872_, v_isTarget_1873_, v_model_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_buckets_1882_; lean_object* v___x_1883_; size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_buckets_1882_ = lean_ctor_get(v_a_1881_, 1);
lean_inc_ref(v_buckets_1882_);
lean_dec(v_a_1881_);
v___x_1883_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1884_ = lean_array_size(v_buckets_1882_);
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1882_, v_sz_1884_, v___x_1885_, v___x_1883_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec_ref(v_buckets_1882_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1872_, v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
return v___x_1886_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1880_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1880_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_finalizeModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1872_ = stack[0].m_obj;
lean_object* v_isTarget_1873_ = stack[1].m_obj;
lean_object* v_model_1874_ = stack[2].m_obj;
lean_object* v_a_1875_ = stack[3].m_obj;
lean_object* v_a_1876_ = stack[4].m_obj;
lean_object* v_a_1877_ = stack[5].m_obj;
lean_object* v_a_1878_ = stack[6].m_obj;
lean_object* v_res_1904_;
v_res_1904_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1872_, v_isTarget_1873_, v_model_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
stack->m_obj
 = v_res_1904_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1905_, lean_object* v_isTarget_1906_, lean_object* v_model_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1905_, v_isTarget_1906_, v_model_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec_ref(v_goal_1905_);
return v_res_1913_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1914_, v_a_1915_);
return v___x_1921_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1914_ = stack[0].m_obj;
lean_object* v_a_1915_ = stack[1].m_obj;
lean_object* v___y_1916_ = stack[2].m_obj;
lean_object* v___y_1917_ = stack[3].m_obj;
lean_object* v___y_1918_ = stack[4].m_obj;
lean_object* v___y_1919_ = stack[5].m_obj;
lean_object* v_res_1922_;
v_res_1922_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1914_, v_a_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
stack->m_obj
 = v_res_1922_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1923_, v_a_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; lean_object* v_env_1938_; uint8_t v___x_1939_; lean_object* v_env_1940_; lean_object* v___x_1941_; lean_object* v_toCold_1942_; lean_object* v_mctx_1943_; lean_object* v_lctx_1944_; lean_object* v_options_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1937_ = lean_st_ref_get(v___y_1935_);
v_env_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc_ref(v_env_1938_);
lean_dec(v___x_1937_);
v___x_1939_ = 0;
v_env_1940_ = l_Lean_Environment_setRecordingDeps(v_env_1938_, v___x_1939_);
v___x_1941_ = lean_st_ref_get(v___y_1933_);
v_toCold_1942_ = lean_ctor_get(v___y_1934_, 0);
v_mctx_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref(v_mctx_1943_);
lean_dec(v___x_1941_);
v_lctx_1944_ = lean_ctor_get(v___y_1932_, 2);
v_options_1945_ = lean_ctor_get(v_toCold_1942_, 2);
lean_inc_ref(v_options_1945_);
lean_inc_ref(v_lctx_1944_);
v___x_1946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1946_, 0, v_env_1940_);
lean_ctor_set(v___x_1946_, 1, v_mctx_1943_);
lean_ctor_set(v___x_1946_, 2, v_lctx_1944_);
lean_ctor_set(v___x_1946_, 3, v_options_1945_);
v___x_1947_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_msgData_1931_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1931_ = stack[0].m_obj;
lean_object* v___y_1932_ = stack[1].m_obj;
lean_object* v___y_1933_ = stack[2].m_obj;
lean_object* v___y_1934_ = stack[3].m_obj;
lean_object* v___y_1935_ = stack[4].m_obj;
lean_object* v_res_1949_;
v_res_1949_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
stack->m_obj
 = v_res_1949_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1957_; double v___x_1958_; 
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_float_of_nat(v___x_1957_);
return v___x_1958_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_ref_1969_; lean_object* v___x_1970_; lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2016_; 
v_ref_1969_ = lean_ctor_get(v___y_1966_, 2);
v___x_1970_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_2016_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2016_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v_traceState_1976_; lean_object* v_env_1977_; lean_object* v_nextMacroScope_1978_; lean_object* v_ngen_1979_; lean_object* v_auxDeclNGen_1980_; lean_object* v_cache_1981_; lean_object* v_recordedDeps_1982_; lean_object* v_messages_1983_; lean_object* v_infoState_1984_; lean_object* v_snapshotTasks_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2015_; 
v___x_1975_ = lean_st_ref_take(v___y_1967_);
v_traceState_1976_ = lean_ctor_get(v___x_1975_, 4);
v_env_1977_ = lean_ctor_get(v___x_1975_, 0);
v_nextMacroScope_1978_ = lean_ctor_get(v___x_1975_, 1);
v_ngen_1979_ = lean_ctor_get(v___x_1975_, 2);
v_auxDeclNGen_1980_ = lean_ctor_get(v___x_1975_, 3);
v_cache_1981_ = lean_ctor_get(v___x_1975_, 5);
v_recordedDeps_1982_ = lean_ctor_get(v___x_1975_, 6);
v_messages_1983_ = lean_ctor_get(v___x_1975_, 7);
v_infoState_1984_ = lean_ctor_get(v___x_1975_, 8);
v_snapshotTasks_1985_ = lean_ctor_get(v___x_1975_, 9);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1987_ = v___x_1975_;
v_isShared_1988_ = v_isSharedCheck_2015_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snapshotTasks_1985_);
lean_inc(v_infoState_1984_);
lean_inc(v_messages_1983_);
lean_inc(v_recordedDeps_1982_);
lean_inc(v_cache_1981_);
lean_inc(v_traceState_1976_);
lean_inc(v_auxDeclNGen_1980_);
lean_inc(v_ngen_1979_);
lean_inc(v_nextMacroScope_1978_);
lean_inc(v_env_1977_);
lean_dec(v___x_1975_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2015_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
uint64_t v_tid_1989_; lean_object* v_traces_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2014_; 
v_tid_1989_ = lean_ctor_get_uint64(v_traceState_1976_, sizeof(void*)*1);
v_traces_1990_ = lean_ctor_get(v_traceState_1976_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_traceState_1976_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1992_ = v_traceState_1976_;
v_isShared_1993_ = v_isSharedCheck_2014_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_traces_1990_);
lean_dec(v_traceState_1976_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2014_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; double v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_box(0);
v___x_1996_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1997_ = 0;
v___x_1998_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1999_, 0, v_cls_1962_);
lean_ctor_set(v___x_1999_, 1, v___x_1995_);
lean_ctor_set(v___x_1999_, 2, v___x_1998_);
lean_ctor_set_float(v___x_1999_, sizeof(void*)*3, v___x_1996_);
lean_ctor_set_float(v___x_1999_, sizeof(void*)*3 + 8, v___x_1996_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*3 + 16, v___x_1997_);
v___x_2000_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_2001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v_a_1971_);
lean_ctor_set(v___x_2001_, 2, v___x_2000_);
lean_inc(v_ref_1969_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_ref_1969_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = l_Lean_PersistentArray_push___redArg(v_traces_1990_, v___x_2002_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2003_);
v___x_2005_ = v___x_1992_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2003_);
lean_ctor_set_uint64(v_reuseFailAlloc_2013_, sizeof(void*)*1, v_tid_1989_);
v___x_2005_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 4, v___x_2005_);
v___x_2007_ = v___x_1987_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_env_1977_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_nextMacroScope_1978_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_ngen_1979_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_auxDeclNGen_1980_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2012_, 5, v_cache_1981_);
lean_ctor_set(v_reuseFailAlloc_2012_, 6, v_recordedDeps_1982_);
lean_ctor_set(v_reuseFailAlloc_2012_, 7, v_messages_1983_);
lean_ctor_set(v_reuseFailAlloc_2012_, 8, v_infoState_1984_);
lean_ctor_set(v_reuseFailAlloc_2012_, 9, v_snapshotTasks_1985_);
v___x_2007_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_st_ref_put(v___y_1967_, v___x_2007_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1994_);
v___x_2010_ = v___x_1973_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1994_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1962_ = stack[0].m_obj;
lean_object* v_msg_1963_ = stack[1].m_obj;
lean_object* v___y_1964_ = stack[2].m_obj;
lean_object* v___y_1965_ = stack[3].m_obj;
lean_object* v___y_1966_ = stack[4].m_obj;
lean_object* v___y_1967_ = stack[5].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1962_, v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_2018_, lean_object* v_msg_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_2018_, v_msg_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2025_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_2030_, lean_object* v_as_2031_, size_t v_sz_2032_, size_t v_i_2033_, lean_object* v_b_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___x_2040_; 
v___x_2040_ = lean_usize_dec_lt(v_i_2033_, v_sz_2032_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v_traceClass_2030_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_b_2034_);
return v___x_2041_;
}
else
{
lean_object* v_a_2042_; lean_object* v_snd_2043_; lean_object* v_fst_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2079_; 
v_a_2042_ = lean_array_uget(v_as_2031_, v_i_2033_);
v_snd_2043_ = lean_ctor_get(v_a_2042_, 1);
v_fst_2044_ = lean_ctor_get(v_a_2042_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_a_2042_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2046_ = v_a_2042_;
v_isShared_2047_ = v_isSharedCheck_2079_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_snd_2043_);
lean_inc(v_fst_2044_);
lean_dec(v_a_2042_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2079_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_num_2048_; lean_object* v_den_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2078_; 
v_num_2048_ = lean_ctor_get(v_snd_2043_, 0);
v_den_2049_ = lean_ctor_get(v_snd_2043_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_snd_2043_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2051_ = v_snd_2043_;
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_den_2049_);
lean_inc(v_num_2048_);
lean_dec(v_snd_2043_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2044_);
v___x_2055_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 7);
lean_ctor_set(v___x_2051_, 1, v___x_2055_);
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2057_ = v___x_2051_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___y_2059_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_nat_dec_eq(v_den_2049_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2071_ = l_Int_repr(v_num_2048_);
lean_dec(v_num_2048_);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2073_ = lean_string_append(v___x_2071_, v___x_2072_);
v___x_2074_ = l_Nat_reprFast(v_den_2049_);
v___x_2075_ = lean_string_append(v___x_2073_, v___x_2074_);
lean_dec_ref(v___x_2074_);
v___y_2059_ = v___x_2075_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2076_; 
lean_dec(v_den_2049_);
v___x_2076_ = l_Int_repr(v_num_2048_);
lean_dec(v_num_2048_);
v___y_2059_ = v___x_2076_;
goto v___jp_2058_;
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___y_2059_);
v___x_2061_ = l_Lean_MessageData_ofFormat(v___x_2060_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 7);
lean_ctor_set(v___x_2046_, 1, v___x_2061_);
lean_ctor_set(v___x_2046_, 0, v___x_2057_);
v___x_2063_ = v___x_2046_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
lean_inc(v_traceClass_2030_);
v___x_2064_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_2030_, v___x_2063_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2064_) == 0)
{
size_t v___x_2065_; size_t v___x_2066_; 
lean_dec_ref_known(v___x_2064_, 1);
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_add(v_i_2033_, v___x_2065_);
v_i_2033_ = v___x_2066_;
v_b_2034_ = v___x_2053_;
goto _start;
}
else
{
lean_dec(v_traceClass_2030_);
return v___x_2064_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_traceClass_2030_ = stack[0].m_obj;
lean_object* v_as_2031_ = stack[1].m_obj;
size_t v_sz_2032_ = stack[2].m_num;
size_t v_i_2033_ = stack[3].m_num;
lean_object* v_b_2034_ = stack[4].m_obj;
lean_object* v___y_2035_ = stack[5].m_obj;
lean_object* v___y_2036_ = stack[6].m_obj;
lean_object* v___y_2037_ = stack[7].m_obj;
lean_object* v___y_2038_ = stack[8].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2030_, v_as_2031_, v_sz_2032_, v_i_2033_, v_b_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2081_, lean_object* v_as_2082_, lean_object* v_sz_2083_, lean_object* v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
size_t v_sz_boxed_2091_; size_t v_i_boxed_2092_; lean_object* v_res_2093_; 
v_sz_boxed_2091_ = lean_unbox_usize(v_sz_2083_);
lean_dec(v_sz_2083_);
v_i_boxed_2092_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2081_, v_as_2082_, v_sz_boxed_2091_, v_i_boxed_2092_, v_b_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v_as_2082_);
return v_res_2093_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2097_, lean_object* v_model_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_toCold_2107_; lean_object* v_options_2108_; uint8_t v_hasTrace_2109_; 
v_toCold_2107_ = lean_ctor_get(v_a_2101_, 0);
v_options_2108_ = lean_ctor_get(v_toCold_2107_, 2);
v_hasTrace_2109_ = lean_ctor_get_uint8(v_options_2108_, sizeof(void*)*1);
if (v_hasTrace_2109_ == 0)
{
lean_dec(v_traceClass_2097_);
goto v___jp_2104_;
}
else
{
lean_object* v_inheritedTraceOptions_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_inheritedTraceOptions_2110_ = lean_ctor_get(v_toCold_2107_, 11);
v___x_2111_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2097_);
v___x_2112_ = l_Lean_Name_append(v___x_2111_, v_traceClass_2097_);
v___x_2113_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2110_, v_options_2108_, v___x_2112_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec(v_traceClass_2097_);
goto v___jp_2104_;
}
else
{
lean_object* v___x_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = lean_box(0);
v_sz_2115_ = lean_array_size(v_model_2098_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2097_, v_model_2098_, v_sz_2115_, v___x_2116_, v___x_2114_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2125_);
v___x_2119_ = v___x_2117_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2114_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2114_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
return v___x_2117_;
}
}
}
v___jp_2104_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_traceModel_0interp(lean_interpreter_value* stack)
{
lean_object* v_traceClass_2097_ = stack[0].m_obj;
lean_object* v_model_2098_ = stack[1].m_obj;
lean_object* v_a_2099_ = stack[2].m_obj;
lean_object* v_a_2100_ = stack[3].m_obj;
lean_object* v_a_2101_ = stack[4].m_obj;
lean_object* v_a_2102_ = stack[5].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2097_, v_model_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2127_, lean_object* v_model_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2127_, v_model_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec_ref(v_model_2128_);
return v_res_2134_;
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
