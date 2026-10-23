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
uint8_t l_Lean_Meta_Grind_Arith_isNatNum(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntNum(lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(lean_object* v_a_36_, lean_object* v_v_37_, lean_object* v_other_38_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object* v_a_46_, lean_object* v_v_47_, lean_object* v_other_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_46_, v_v_47_, v_other_48_);
lean_dec_ref(v_other_48_);
lean_dec_ref(v_a_46_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object* v_00_u03b2_51_, lean_object* v_m_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_52_, v_a_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object* v_00_u03b2_55_, lean_object* v_m_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_55_, v_m_56_, v_a_57_);
lean_dec_ref(v_a_57_);
lean_dec_ref(v_m_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object* v_00_u03b2_59_, lean_object* v_a_60_, lean_object* v_x_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object* v_00_u03b2_63_, lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_63_, v_a_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec_ref(v_a_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object* v_goal_76_, lean_object* v_e_77_, lean_object* v_a_78_, lean_object* v_v_79_, lean_object* v_as_x27_80_, lean_object* v_b_81_){
_start:
{
if (lean_obj_tag(v_as_x27_80_) == 0)
{
lean_dec(v_v_79_);
lean_inc_ref(v_b_81_);
return v_b_81_;
}
else
{
lean_object* v_head_82_; lean_object* v_tail_83_; lean_object* v___x_84_; uint8_t v___y_86_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_head_82_ = lean_ctor_get(v_as_x27_80_, 0);
v_tail_83_ = lean_ctor_get(v_as_x27_80_, 1);
v___x_84_ = lean_box(0);
v___x_90_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_82_);
v___x_91_ = l_Lean_Expr_cleanupAnnotations(v_head_82_);
v___x_92_ = l_Lean_Expr_isApp(v___x_91_);
if (v___x_92_ == 0)
{
lean_dec_ref(v___x_91_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_object* v_arg_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_arg_94_ = lean_ctor_get(v___x_91_, 1);
lean_inc_ref(v_arg_94_);
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_91_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_dec_ref(v___x_95_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_object* v_arg_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_arg_98_ = lean_ctor_get(v___x_95_, 1);
lean_inc_ref(v_arg_98_);
v___x_99_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
v___x_100_ = l_Lean_Expr_isApp(v___x_99_);
if (v___x_100_ == 0)
{
lean_dec_ref(v___x_99_);
lean_dec_ref(v_arg_98_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_99_);
v___x_103_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_104_ = l_Lean_Expr_isConstOf(v___x_102_, v___x_103_);
lean_dec_ref(v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_arg_98_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_76_, v_head_82_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_109_ = l_Lean_Expr_isConstOf(v_val_107_, v___x_108_);
lean_dec(v_val_107_);
if (v___x_109_ == 0)
{
lean_dec_ref(v_arg_98_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_76_, v_arg_98_);
lean_dec_ref(v_arg_98_);
if (lean_obj_tag(v___x_111_) == 1)
{
lean_object* v_val_112_; lean_object* v___x_113_; 
v_val_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_76_, v_arg_94_);
lean_dec_ref(v_arg_94_);
if (lean_obj_tag(v___x_113_) == 1)
{
lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_132_; 
v_val_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_132_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_132_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_132_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___y_119_; uint8_t v___x_124_; 
v___x_124_ = lean_expr_eqv(v_val_112_, v_e_77_);
if (v___x_124_ == 0)
{
lean_del_object(v___x_116_);
v___y_119_ = v___x_124_;
goto v___jp_118_;
}
else
{
uint8_t v___x_125_; 
lean_inc(v_v_79_);
v___x_125_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_78_, v_v_79_, v_val_114_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_val_114_);
lean_dec(v_val_112_);
lean_dec(v_v_79_);
v___x_126_ = lean_box(v___x_125_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_126_);
v___x_128_ = v___x_116_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_84_);
return v___x_129_;
}
}
else
{
uint8_t v___x_131_; 
lean_del_object(v___x_116_);
v___x_131_ = 0;
v___y_119_ = v___x_131_;
goto v___jp_118_;
}
}
v___jp_118_:
{
uint8_t v___x_120_; 
v___x_120_ = lean_expr_eqv(v_val_114_, v_e_77_);
lean_dec(v_val_114_);
if (v___x_120_ == 0)
{
lean_dec(v_val_112_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
uint8_t v___x_122_; 
lean_inc(v_v_79_);
v___x_122_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_78_, v_v_79_, v_val_112_);
lean_dec(v_val_112_);
if (v___x_122_ == 0)
{
lean_dec(v_v_79_);
v___y_86_ = v___y_119_;
goto v___jp_85_;
}
else
{
if (v___y_119_ == 0)
{
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
else
{
lean_dec(v_v_79_);
v___y_86_ = v___y_119_;
goto v___jp_85_;
}
}
}
}
}
}
else
{
lean_dec(v___x_113_);
lean_dec(v_val_112_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
}
else
{
lean_dec(v___x_111_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
}
}
else
{
lean_dec(v___x_106_);
lean_dec_ref(v_arg_98_);
lean_dec_ref(v_arg_94_);
v_as_x27_80_ = v_tail_83_;
v_b_81_ = v___x_90_;
goto _start;
}
}
}
}
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(v___y_86_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_84_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_136_, lean_object* v_e_137_, lean_object* v_a_138_, lean_object* v_v_139_, lean_object* v_as_x27_140_, lean_object* v_b_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_136_, v_e_137_, v_a_138_, v_v_139_, v_as_x27_140_, v_b_141_);
lean_dec_ref(v_b_141_);
lean_dec(v_as_x27_140_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_e_137_);
lean_dec_ref(v_goal_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_143_, lean_object* v_vals_144_, lean_object* v_i_145_, lean_object* v_k_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_array_get_size(v_keys_143_);
v___x_148_ = lean_nat_dec_lt(v_i_145_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
lean_dec(v_i_145_);
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
lean_object* v_k_x27_150_; size_t v___x_151_; size_t v___x_152_; uint8_t v___x_153_; 
v_k_x27_150_ = lean_array_fget_borrowed(v_keys_143_, v_i_145_);
v___x_151_ = lean_ptr_addr(v_k_146_);
v___x_152_ = lean_ptr_addr(v_k_x27_150_);
v___x_153_ = lean_usize_dec_eq(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_i_145_, v___x_154_);
lean_dec(v_i_145_);
v_i_145_ = v___x_155_;
goto _start;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_array_fget_borrowed(v_vals_144_, v_i_145_);
lean_dec(v_i_145_);
lean_inc(v___x_157_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_k_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_159_, v_vals_160_, v_i_161_, v_k_162_);
lean_dec_ref(v_k_162_);
lean_dec_ref(v_vals_160_);
lean_dec_ref(v_keys_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_164_, size_t v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_es_167_; lean_object* v___x_168_; size_t v___x_169_; size_t v___x_170_; lean_object* v_j_171_; lean_object* v___x_172_; 
v_es_167_ = lean_ctor_get(v_x_164_, 0);
v___x_168_ = lean_box(2);
v___x_169_ = ((size_t)31ULL);
v___x_170_ = lean_usize_land(v_x_165_, v___x_169_);
v_j_171_ = lean_usize_to_nat(v___x_170_);
v___x_172_ = lean_array_get_borrowed(v___x_168_, v_es_167_, v_j_171_);
lean_dec(v_j_171_);
switch(lean_obj_tag(v___x_172_))
{
case 0:
{
lean_object* v_key_173_; lean_object* v_val_174_; size_t v___x_175_; size_t v___x_176_; uint8_t v___x_177_; 
v_key_173_ = lean_ctor_get(v___x_172_, 0);
v_val_174_ = lean_ctor_get(v___x_172_, 1);
v___x_175_ = lean_ptr_addr(v_x_166_);
v___x_176_ = lean_ptr_addr(v_key_173_);
v___x_177_ = lean_usize_dec_eq(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
lean_inc(v_val_174_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_val_174_);
return v___x_179_;
}
}
case 1:
{
lean_object* v_node_180_; size_t v___x_181_; size_t v___x_182_; 
v_node_180_ = lean_ctor_get(v___x_172_, 0);
v___x_181_ = ((size_t)5ULL);
v___x_182_ = lean_usize_shift_right(v_x_165_, v___x_181_);
v_x_164_ = v_node_180_;
v_x_165_ = v___x_182_;
goto _start;
}
default: 
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
else
{
lean_object* v_ks_185_; lean_object* v_vs_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_ks_185_ = lean_ctor_get(v_x_164_, 0);
v_vs_186_ = lean_ctor_get(v_x_164_, 1);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_185_, v_vs_186_, v___x_187_, v_x_166_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_1746__boxed_192_; lean_object* v_res_193_; 
v_x_1746__boxed_192_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_193_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_189_, v_x_1746__boxed_192_, v_x_191_);
lean_dec_ref(v_x_191_);
lean_dec_ref(v_x_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; uint64_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_196_ = lean_ptr_addr(v_x_195_);
v___x_197_ = ((size_t)3ULL);
v___x_198_ = lean_usize_shift_right(v___x_196_, v___x_197_);
v___x_199_ = lean_usize_to_uint64(v___x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_194_, v___x_200_, v_x_195_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_202_, v_x_203_);
lean_dec_ref(v_x_203_);
lean_dec_ref(v_x_202_);
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_205_, lean_object* v_a_206_, lean_object* v_e_207_, lean_object* v_v_208_){
_start:
{
lean_object* v_toGoalState_209_; lean_object* v_parents_210_; lean_object* v___x_211_; 
v_toGoalState_209_ = lean_ctor_get(v_goal_205_, 0);
v_parents_210_ = lean_ctor_get(v_toGoalState_209_, 3);
v___x_211_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_210_, v_e_207_);
if (lean_obj_tag(v___x_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_fst_216_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_212_);
lean_dec(v_val_212_);
v___x_214_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_215_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_205_, v_e_207_, v_a_206_, v_v_208_, v___x_213_, v___x_214_);
lean_dec(v___x_213_);
v_fst_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_fst_216_);
lean_dec_ref(v___x_215_);
if (lean_obj_tag(v_fst_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = 1;
return v___x_217_;
}
else
{
lean_object* v_val_218_; uint8_t v___x_219_; 
v_val_218_ = lean_ctor_get(v_fst_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_fst_216_, 1);
v___x_219_ = lean_unbox(v_val_218_);
lean_dec(v_val_218_);
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
lean_dec(v___x_211_);
lean_dec(v_v_208_);
v___x_220_ = 1;
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_221_, lean_object* v_a_222_, lean_object* v_e_223_, lean_object* v_v_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_221_, v_a_222_, v_e_223_, v_v_224_);
lean_dec_ref(v_e_223_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_goal_221_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_228_, v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_231_, v_x_232_, v_x_233_);
lean_dec_ref(v_x_233_);
lean_dec_ref(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_235_, lean_object* v_e_236_, lean_object* v_a_237_, lean_object* v_v_238_, lean_object* v_as_239_, lean_object* v_as_x27_240_, lean_object* v_b_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_235_, v_e_236_, v_a_237_, v_v_238_, v_as_x27_240_, v_b_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_244_, lean_object* v_e_245_, lean_object* v_a_246_, lean_object* v_v_247_, lean_object* v_as_248_, lean_object* v_as_x27_249_, lean_object* v_b_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_244_, v_e_245_, v_a_246_, v_v_247_, v_as_248_, v_as_x27_249_, v_b_250_, v_a_251_);
lean_dec_ref(v_b_250_);
lean_dec(v_as_x27_249_);
lean_dec(v_as_248_);
lean_dec_ref(v_a_246_);
lean_dec_ref(v_e_245_);
lean_dec_ref(v_goal_244_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_253_, lean_object* v_x_254_, size_t v_x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_254_, v_x_255_, v_x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
size_t v_x_1851__boxed_262_; lean_object* v_res_263_; 
v_x_1851__boxed_262_ = lean_unbox_usize(v_x_260_);
lean_dec(v_x_260_);
v_res_263_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_258_, v_x_259_, v_x_1851__boxed_262_, v_x_261_);
lean_dec_ref(v_x_261_);
lean_dec_ref(v_x_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_264_, lean_object* v_keys_265_, lean_object* v_vals_266_, lean_object* v_heq_267_, lean_object* v_i_268_, lean_object* v_k_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_265_, v_vals_266_, v_i_268_, v_k_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_271_, lean_object* v_keys_272_, lean_object* v_vals_273_, lean_object* v_heq_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_271_, v_keys_272_, v_vals_273_, v_heq_274_, v_i_275_, v_k_276_);
lean_dec_ref(v_k_276_);
lean_dec_ref(v_vals_273_);
lean_dec_ref(v_keys_272_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
else
{
lean_object* v_key_281_; lean_object* v_tail_282_; uint8_t v___x_283_; 
v_key_281_ = lean_ctor_get(v_x_279_, 0);
v_tail_282_ = lean_ctor_get(v_x_279_, 2);
v___x_283_ = lean_int_dec_eq(v_key_281_, v_a_278_);
if (v___x_283_ == 0)
{
v_x_279_ = v_tail_282_;
goto _start;
}
else
{
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_285_, lean_object* v_x_286_){
_start:
{
uint8_t v_res_287_; lean_object* v_r_288_; 
v_res_287_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_285_, v_x_286_);
lean_dec(v_x_286_);
lean_dec(v_a_285_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_289_; lean_object* v_intZero_290_; 
v_natZero_289_ = lean_unsigned_to_nat(0u);
v_intZero_290_ = lean_nat_to_int(v_natZero_289_);
return v_intZero_290_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_buckets_293_; lean_object* v___x_294_; uint64_t v___y_296_; lean_object* v_intZero_310_; uint8_t v_isNeg_311_; 
v_buckets_293_ = lean_ctor_get(v_m_291_, 1);
v___x_294_ = lean_array_get_size(v_buckets_293_);
v_intZero_310_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_311_ = lean_int_dec_lt(v_a_292_, v_intZero_310_);
if (v_isNeg_311_ == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint64_t v___x_315_; 
v_a_312_ = lean_nat_abs(v_a_292_);
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_mul(v___x_313_, v_a_312_);
lean_dec(v_a_312_);
v___x_315_ = lean_uint64_of_nat(v___x_314_);
lean_dec(v___x_314_);
v___y_296_ = v___x_315_;
goto v___jp_295_;
}
else
{
lean_object* v_abs_316_; lean_object* v_one_317_; lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint64_t v___x_322_; 
v_abs_316_ = lean_nat_abs(v_a_292_);
v_one_317_ = lean_unsigned_to_nat(1u);
v_a_318_ = lean_nat_sub(v_abs_316_, v_one_317_);
lean_dec(v_abs_316_);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_mul(v___x_319_, v_a_318_);
lean_dec(v_a_318_);
v___x_321_ = lean_nat_add(v___x_320_, v_one_317_);
lean_dec(v___x_320_);
v___x_322_ = lean_uint64_of_nat(v___x_321_);
lean_dec(v___x_321_);
v___y_296_ = v___x_322_;
goto v___jp_295_;
}
v___jp_295_:
{
uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v_fold_299_; uint64_t v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_297_ = 32ULL;
v___x_298_ = lean_uint64_shift_right(v___y_296_, v___x_297_);
v_fold_299_ = lean_uint64_xor(v___y_296_, v___x_298_);
v___x_300_ = 16ULL;
v___x_301_ = lean_uint64_shift_right(v_fold_299_, v___x_300_);
v___x_302_ = lean_uint64_xor(v_fold_299_, v___x_301_);
v___x_303_ = lean_uint64_to_usize(v___x_302_);
v___x_304_ = lean_usize_of_nat(v___x_294_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_sub(v___x_304_, v___x_305_);
v___x_307_ = lean_usize_land(v___x_303_, v___x_306_);
v___x_308_ = lean_array_uget_borrowed(v_buckets_293_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_292_, v___x_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_m_323_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_329_, lean_object* v_a_330_, lean_object* v_e_331_, lean_object* v_alreadyUsed_332_, lean_object* v_next_333_){
_start:
{
uint8_t v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_332_, v_next_333_);
if (v___x_334_ == 0)
{
uint8_t v___x_335_; 
lean_inc(v_next_333_);
v___x_335_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_329_, v_a_330_, v_e_331_, v_next_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_337_ = lean_int_add(v_next_333_, v___x_336_);
lean_dec(v_next_333_);
v_next_333_ = v___x_337_;
goto _start;
}
else
{
return v_next_333_;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_340_ = lean_int_add(v_next_333_, v___x_339_);
lean_dec(v_next_333_);
v_next_333_ = v___x_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_342_, lean_object* v_a_343_, lean_object* v_e_344_, lean_object* v_alreadyUsed_345_, lean_object* v_next_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_342_, v_a_343_, v_e_344_, v_alreadyUsed_345_, v_next_346_);
lean_dec_ref(v_alreadyUsed_345_);
lean_dec_ref(v_e_344_);
lean_dec_ref(v_a_343_);
lean_dec_ref(v_goal_342_);
return v_res_347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_348_, lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_349_, v_a_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_352_, lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_352_, v_m_353_, v_a_354_);
lean_dec(v_a_354_);
lean_dec_ref(v_m_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_357_, lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_361_, lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_361_, v_a_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec(v_a_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_366_, lean_object* v_a_367_, lean_object* v_e_368_, lean_object* v_next_369_, lean_object* v_alreadyUsed_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_366_, v_a_367_, v_e_368_, v_alreadyUsed_370_, v_next_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_372_, lean_object* v_a_373_, lean_object* v_e_374_, lean_object* v_next_375_, lean_object* v_alreadyUsed_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_372_, v_a_373_, v_e_374_, v_next_375_, v_alreadyUsed_376_);
lean_dec_ref(v_alreadyUsed_376_);
lean_dec_ref(v_e_374_);
lean_dec_ref(v_a_373_);
lean_dec_ref(v_goal_372_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_463_){
_start:
{
uint8_t v___x_469_; 
lean_inc_ref(v_e_463_);
v___x_469_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_463_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; 
lean_inc_ref(v_e_463_);
v___x_470_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_463_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7));
v___x_472_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10));
v___x_474_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13));
v___x_476_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16));
v___x_478_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19));
v___x_480_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22));
v___x_482_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25));
v___x_484_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28));
v___x_486_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31));
v___x_488_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34));
v___x_490_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37));
v___x_492_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Expr_isIte(v_e_463_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = l_Lean_Expr_isDIte(v_e_463_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_496_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_498_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49));
v___x_500_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_499_);
if (v___x_500_ == 0)
{
if (lean_obj_tag(v_e_463_) == 9)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v_e_463_, 0);
if (lean_obj_tag(v_a_501_) == 0)
{
uint8_t v___x_502_; 
lean_dec_ref_known(v_e_463_, 1);
v___x_502_ = 1;
return v___x_502_;
}
else
{
goto v___jp_464_;
}
}
else
{
goto v___jp_464_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_500_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_498_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_494_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_493_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_492_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_490_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_484_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_480_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_476_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_474_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_472_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_470_;
}
}
else
{
lean_dec_ref(v_e_463_);
return v___x_469_;
}
v___jp_464_:
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_466_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4));
v___x_468_ = l_Lean_Expr_isAppOf(v_e_463_, v___x_467_);
lean_dec_ref(v_e_463_);
return v___x_468_;
}
else
{
lean_dec_ref(v_e_463_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
return v_x_506_;
}
else
{
lean_object* v_key_508_; lean_object* v_value_509_; lean_object* v_tail_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_533_; 
v_key_508_ = lean_ctor_get(v_x_507_, 0);
v_value_509_ = lean_ctor_get(v_x_507_, 1);
v_tail_510_ = lean_ctor_get(v_x_507_, 2);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_507_);
if (v_isSharedCheck_533_ == 0)
{
v___x_512_ = v_x_507_;
v_isShared_513_ = v_isSharedCheck_533_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_tail_510_);
lean_inc(v_value_509_);
lean_inc(v_key_508_);
lean_dec(v_x_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_533_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v_fold_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_514_ = lean_array_get_size(v_x_506_);
v___x_515_ = l_Lean_Expr_hash(v_key_508_);
v___x_516_ = 32ULL;
v___x_517_ = lean_uint64_shift_right(v___x_515_, v___x_516_);
v_fold_518_ = lean_uint64_xor(v___x_515_, v___x_517_);
v___x_519_ = 16ULL;
v___x_520_ = lean_uint64_shift_right(v_fold_518_, v___x_519_);
v___x_521_ = lean_uint64_xor(v_fold_518_, v___x_520_);
v___x_522_ = lean_uint64_to_usize(v___x_521_);
v___x_523_ = lean_usize_of_nat(v___x_514_);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_sub(v___x_523_, v___x_524_);
v___x_526_ = lean_usize_land(v___x_522_, v___x_525_);
v___x_527_ = lean_array_uget_borrowed(v_x_506_, v___x_526_);
lean_inc(v___x_527_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 2, v___x_527_);
v___x_529_ = v___x_512_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_key_508_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_value_509_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v___x_527_);
v___x_529_ = v_reuseFailAlloc_532_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_array_uset(v_x_506_, v___x_526_, v___x_529_);
v_x_506_ = v___x_530_;
v_x_507_ = v_tail_510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_534_, lean_object* v_source_535_, lean_object* v_target_536_){
_start:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_source_535_);
v___x_538_ = lean_nat_dec_lt(v_i_534_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec_ref(v_source_535_);
lean_dec(v_i_534_);
return v_target_536_;
}
else
{
lean_object* v_es_539_; lean_object* v___x_540_; lean_object* v_source_541_; lean_object* v_target_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_es_539_ = lean_array_fget(v_source_535_, v_i_534_);
v___x_540_ = lean_box(0);
v_source_541_ = lean_array_fset(v_source_535_, v_i_534_, v___x_540_);
v_target_542_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_536_, v_es_539_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_i_534_, v___x_543_);
lean_dec(v_i_534_);
v_i_534_ = v___x_544_;
v_source_535_ = v_source_541_;
v_target_536_ = v_target_542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_nbuckets_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_547_ = lean_array_get_size(v_data_546_);
v___x_548_ = lean_unsigned_to_nat(2u);
v_nbuckets_549_ = lean_nat_mul(v___x_547_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_box(0);
v___x_552_ = lean_mk_array(v_nbuckets_549_, v___x_551_);
v___x_553_ = lean_array_propagate_mark(v_data_546_, v___x_552_);
v___x_554_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_550_, v_data_546_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_555_, lean_object* v_b_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_dec(v_b_556_);
lean_dec_ref(v_a_555_);
return v_x_557_;
}
else
{
lean_object* v_key_558_; lean_object* v_value_559_; lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_572_; 
v_key_558_ = lean_ctor_get(v_x_557_, 0);
v_value_559_ = lean_ctor_get(v_x_557_, 1);
v_tail_560_ = lean_ctor_get(v_x_557_, 2);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_572_ == 0)
{
v___x_562_ = v_x_557_;
v_isShared_563_ = v_isSharedCheck_572_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_inc(v_value_559_);
lean_inc(v_key_558_);
lean_dec(v_x_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_572_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
uint8_t v___x_564_; 
v___x_564_ = lean_expr_eqv(v_key_558_, v_a_555_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_555_, v_b_556_, v_tail_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_key_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_value_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_object* v___x_570_; 
lean_dec(v_value_559_);
lean_dec(v_key_558_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_b_556_);
lean_ctor_set(v___x_562_, 0, v_a_555_);
v___x_570_ = v___x_562_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_555_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_b_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_tail_560_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
uint8_t v___x_575_; 
v___x_575_ = 0;
return v___x_575_;
}
else
{
lean_object* v_key_576_; lean_object* v_tail_577_; uint8_t v___x_578_; 
v_key_576_ = lean_ctor_get(v_x_574_, 0);
v_tail_577_ = lean_ctor_get(v_x_574_, 2);
v___x_578_ = lean_expr_eqv(v_key_576_, v_a_573_);
if (v___x_578_ == 0)
{
v_x_574_ = v_tail_577_;
goto _start;
}
else
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_580_, lean_object* v_x_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_580_, v_x_581_);
lean_dec(v_x_581_);
lean_dec_ref(v_a_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_584_, lean_object* v_a_585_, lean_object* v_b_586_){
_start:
{
lean_object* v_size_587_; lean_object* v_buckets_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_631_; 
v_size_587_ = lean_ctor_get(v_m_584_, 0);
v_buckets_588_ = lean_ctor_get(v_m_584_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_m_584_);
if (v_isSharedCheck_631_ == 0)
{
v___x_590_ = v_m_584_;
v_isShared_591_ = v_isSharedCheck_631_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_buckets_588_);
lean_inc(v_size_587_);
lean_dec(v_m_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_631_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v_fold_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v_bkt_605_; uint8_t v___x_606_; 
v___x_592_ = lean_array_get_size(v_buckets_588_);
v___x_593_ = l_Lean_Expr_hash(v_a_585_);
v___x_594_ = 32ULL;
v___x_595_ = lean_uint64_shift_right(v___x_593_, v___x_594_);
v_fold_596_ = lean_uint64_xor(v___x_593_, v___x_595_);
v___x_597_ = 16ULL;
v___x_598_ = lean_uint64_shift_right(v_fold_596_, v___x_597_);
v___x_599_ = lean_uint64_xor(v_fold_596_, v___x_598_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = lean_usize_of_nat(v___x_592_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_sub(v___x_601_, v___x_602_);
v___x_604_ = lean_usize_land(v___x_600_, v___x_603_);
v_bkt_605_ = lean_array_uget_borrowed(v_buckets_588_, v___x_604_);
v___x_606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_585_, v_bkt_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v_size_x27_608_; lean_object* v___x_609_; lean_object* v_buckets_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_607_ = lean_unsigned_to_nat(1u);
v_size_x27_608_ = lean_nat_add(v_size_587_, v___x_607_);
lean_dec(v_size_587_);
lean_inc(v_bkt_605_);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v_a_585_);
lean_ctor_set(v___x_609_, 1, v_b_586_);
lean_ctor_set(v___x_609_, 2, v_bkt_605_);
v_buckets_x27_610_ = lean_array_uset(v_buckets_588_, v___x_604_, v___x_609_);
v___x_611_ = lean_unsigned_to_nat(4u);
v___x_612_ = lean_nat_mul(v_size_x27_608_, v___x_611_);
v___x_613_ = lean_unsigned_to_nat(3u);
v___x_614_ = lean_nat_div(v___x_612_, v___x_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_array_get_size(v_buckets_x27_610_);
v___x_616_ = lean_nat_dec_le(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
if (v___x_616_ == 0)
{
lean_object* v_val_617_; lean_object* v___x_619_; 
v_val_617_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_610_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_val_617_);
lean_ctor_set(v___x_590_, 0, v_size_x27_608_);
v___x_619_ = v___x_590_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_size_x27_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_val_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v___x_622_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_buckets_x27_610_);
lean_ctor_set(v___x_590_, 0, v_size_x27_608_);
v___x_622_ = v___x_590_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_size_x27_608_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_buckets_x27_610_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v_buckets_x27_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc(v_bkt_605_);
v___x_624_ = lean_box(0);
v_buckets_x27_625_ = lean_array_uset(v_buckets_588_, v___x_604_, v___x_624_);
v___x_626_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_585_, v_b_586_, v_bkt_605_);
v___x_627_ = lean_array_uset(v_buckets_x27_625_, v___x_604_, v___x_626_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_627_);
v___x_629_ = v___x_590_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_size_587_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_632_, lean_object* v_as_x27_633_, lean_object* v_b_634_){
_start:
{
if (lean_obj_tag(v_as_x27_633_) == 0)
{
lean_dec_ref(v_v_632_);
return v_b_634_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_637_; 
v_head_635_ = lean_ctor_get(v_as_x27_633_, 0);
v_tail_636_ = lean_ctor_get(v_as_x27_633_, 1);
lean_inc_ref(v_v_632_);
lean_inc(v_head_635_);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_634_, v_head_635_, v_v_632_);
v_as_x27_633_ = v_tail_636_;
v_b_634_ = v___x_637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_639_, lean_object* v_as_x27_640_, lean_object* v_b_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_639_, v_as_x27_640_, v_b_641_);
lean_dec(v_as_x27_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_643_, lean_object* v_e_644_, lean_object* v_v_645_, lean_object* v_a_646_){
_start:
{
uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = 0;
v___x_648_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_643_, v_e_644_, v___x_647_);
v___x_649_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_645_, v___x_648_, v_a_646_);
lean_dec(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_650_, lean_object* v_e_651_, lean_object* v_v_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_650_, v_e_651_, v_v_652_, v_a_653_);
lean_dec_ref(v_goal_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_655_, lean_object* v_m_656_, lean_object* v_a_657_, lean_object* v_b_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_656_, v_a_657_, v_b_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_660_, lean_object* v_as_661_, lean_object* v_as_x27_662_, lean_object* v_b_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_660_, v_as_x27_662_, v_b_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_666_, lean_object* v_as_667_, lean_object* v_as_x27_668_, lean_object* v_b_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_666_, v_as_667_, v_as_x27_668_, v_b_669_, v_a_670_);
lean_dec(v_as_x27_668_);
lean_dec(v_as_667_);
return v_res_671_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_676_, lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_676_, v_a_677_, v_x_678_);
lean_dec(v_x_678_);
lean_dec_ref(v_a_677_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_681_, lean_object* v_data_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_685_, v_b_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_689_, lean_object* v_i_690_, lean_object* v_source_691_, lean_object* v_target_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_690_, v_source_691_, v_target_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_695_, v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
return v_x_698_;
}
else
{
lean_object* v_key_700_; lean_object* v_value_701_; lean_object* v_tail_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_739_; 
v_key_700_ = lean_ctor_get(v_x_699_, 0);
v_value_701_ = lean_ctor_get(v_x_699_, 1);
v_tail_702_ = lean_ctor_get(v_x_699_, 2);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_739_ == 0)
{
v___x_704_ = v_x_699_;
v_isShared_705_ = v_isSharedCheck_739_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_tail_702_);
lean_inc(v_value_701_);
lean_inc(v_key_700_);
lean_dec(v_x_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_739_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; uint64_t v___y_708_; lean_object* v_intZero_726_; uint8_t v_isNeg_727_; 
v___x_706_ = lean_array_get_size(v_x_698_);
v_intZero_726_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_727_ = lean_int_dec_lt(v_key_700_, v_intZero_726_);
if (v_isNeg_727_ == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint64_t v___x_731_; 
v_a_728_ = lean_nat_abs(v_key_700_);
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_mul(v___x_729_, v_a_728_);
lean_dec(v_a_728_);
v___x_731_ = lean_uint64_of_nat(v___x_730_);
lean_dec(v___x_730_);
v___y_708_ = v___x_731_;
goto v___jp_707_;
}
else
{
lean_object* v_abs_732_; lean_object* v_one_733_; lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint64_t v___x_738_; 
v_abs_732_ = lean_nat_abs(v_key_700_);
v_one_733_ = lean_unsigned_to_nat(1u);
v_a_734_ = lean_nat_sub(v_abs_732_, v_one_733_);
lean_dec(v_abs_732_);
v___x_735_ = lean_unsigned_to_nat(2u);
v___x_736_ = lean_nat_mul(v___x_735_, v_a_734_);
lean_dec(v_a_734_);
v___x_737_ = lean_nat_add(v___x_736_, v_one_733_);
lean_dec(v___x_736_);
v___x_738_ = lean_uint64_of_nat(v___x_737_);
lean_dec(v___x_737_);
v___y_708_ = v___x_738_;
goto v___jp_707_;
}
v___jp_707_:
{
uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v_fold_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_709_ = 32ULL;
v___x_710_ = lean_uint64_shift_right(v___y_708_, v___x_709_);
v_fold_711_ = lean_uint64_xor(v___y_708_, v___x_710_);
v___x_712_ = 16ULL;
v___x_713_ = lean_uint64_shift_right(v_fold_711_, v___x_712_);
v___x_714_ = lean_uint64_xor(v_fold_711_, v___x_713_);
v___x_715_ = lean_uint64_to_usize(v___x_714_);
v___x_716_ = lean_usize_of_nat(v___x_706_);
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_sub(v___x_716_, v___x_717_);
v___x_719_ = lean_usize_land(v___x_715_, v___x_718_);
v___x_720_ = lean_array_uget_borrowed(v_x_698_, v___x_719_);
lean_inc(v___x_720_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 2, v___x_720_);
v___x_722_ = v___x_704_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_key_700_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_value_701_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v___x_720_);
v___x_722_ = v_reuseFailAlloc_725_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; 
v___x_723_ = lean_array_uset(v_x_698_, v___x_719_, v___x_722_);
v_x_698_ = v___x_723_;
v_x_699_ = v_tail_702_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_740_, lean_object* v_source_741_, lean_object* v_target_742_){
_start:
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = lean_array_get_size(v_source_741_);
v___x_744_ = lean_nat_dec_lt(v_i_740_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec_ref(v_source_741_);
lean_dec(v_i_740_);
return v_target_742_;
}
else
{
lean_object* v_es_745_; lean_object* v___x_746_; lean_object* v_source_747_; lean_object* v_target_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_es_745_ = lean_array_fget(v_source_741_, v_i_740_);
v___x_746_ = lean_box(0);
v_source_747_ = lean_array_fset(v_source_741_, v_i_740_, v___x_746_);
v_target_748_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_742_, v_es_745_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_i_740_, v___x_749_);
lean_dec(v_i_740_);
v_i_740_ = v___x_750_;
v_source_741_ = v_source_747_;
v_target_742_ = v_target_748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_nbuckets_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_753_ = lean_array_get_size(v_data_752_);
v___x_754_ = lean_unsigned_to_nat(2u);
v_nbuckets_755_ = lean_nat_mul(v___x_753_, v___x_754_);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_box(0);
v___x_758_ = lean_mk_array(v_nbuckets_755_, v___x_757_);
v___x_759_ = lean_array_propagate_mark(v_data_752_, v___x_758_);
v___x_760_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_756_, v_data_752_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_761_, lean_object* v_a_762_, lean_object* v_b_763_){
_start:
{
lean_object* v_size_764_; lean_object* v_buckets_765_; lean_object* v___x_766_; uint64_t v___y_768_; lean_object* v_intZero_805_; uint8_t v_isNeg_806_; 
v_size_764_ = lean_ctor_get(v_m_761_, 0);
v_buckets_765_ = lean_ctor_get(v_m_761_, 1);
v___x_766_ = lean_array_get_size(v_buckets_765_);
v_intZero_805_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_806_ = lean_int_dec_lt(v_a_762_, v_intZero_805_);
if (v_isNeg_806_ == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint64_t v___x_810_; 
v_a_807_ = lean_nat_abs(v_a_762_);
v___x_808_ = lean_unsigned_to_nat(2u);
v___x_809_ = lean_nat_mul(v___x_808_, v_a_807_);
lean_dec(v_a_807_);
v___x_810_ = lean_uint64_of_nat(v___x_809_);
lean_dec(v___x_809_);
v___y_768_ = v___x_810_;
goto v___jp_767_;
}
else
{
lean_object* v_abs_811_; lean_object* v_one_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint64_t v___x_817_; 
v_abs_811_ = lean_nat_abs(v_a_762_);
v_one_812_ = lean_unsigned_to_nat(1u);
v_a_813_ = lean_nat_sub(v_abs_811_, v_one_812_);
lean_dec(v_abs_811_);
v___x_814_ = lean_unsigned_to_nat(2u);
v___x_815_ = lean_nat_mul(v___x_814_, v_a_813_);
lean_dec(v_a_813_);
v___x_816_ = lean_nat_add(v___x_815_, v_one_812_);
lean_dec(v___x_815_);
v___x_817_ = lean_uint64_of_nat(v___x_816_);
lean_dec(v___x_816_);
v___y_768_ = v___x_817_;
goto v___jp_767_;
}
v___jp_767_:
{
uint64_t v___x_769_; uint64_t v___x_770_; uint64_t v_fold_771_; uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; lean_object* v_bkt_780_; uint8_t v___x_781_; 
v___x_769_ = 32ULL;
v___x_770_ = lean_uint64_shift_right(v___y_768_, v___x_769_);
v_fold_771_ = lean_uint64_xor(v___y_768_, v___x_770_);
v___x_772_ = 16ULL;
v___x_773_ = lean_uint64_shift_right(v_fold_771_, v___x_772_);
v___x_774_ = lean_uint64_xor(v_fold_771_, v___x_773_);
v___x_775_ = lean_uint64_to_usize(v___x_774_);
v___x_776_ = lean_usize_of_nat(v___x_766_);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_sub(v___x_776_, v___x_777_);
v___x_779_ = lean_usize_land(v___x_775_, v___x_778_);
v_bkt_780_ = lean_array_uget_borrowed(v_buckets_765_, v___x_779_);
v___x_781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_762_, v_bkt_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_802_; 
lean_inc_ref(v_buckets_765_);
lean_inc(v_size_764_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_m_761_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; 
v_unused_803_ = lean_ctor_get(v_m_761_, 1);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_m_761_, 0);
lean_dec(v_unused_804_);
v___x_783_ = v_m_761_;
v_isShared_784_ = v_isSharedCheck_802_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_m_761_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_802_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v_size_x27_786_; lean_object* v___x_787_; lean_object* v_buckets_x27_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v_size_x27_786_ = lean_nat_add(v_size_764_, v___x_785_);
lean_dec(v_size_764_);
lean_inc(v_bkt_780_);
v___x_787_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_787_, 0, v_a_762_);
lean_ctor_set(v___x_787_, 1, v_b_763_);
lean_ctor_set(v___x_787_, 2, v_bkt_780_);
v_buckets_x27_788_ = lean_array_uset(v_buckets_765_, v___x_779_, v___x_787_);
v___x_789_ = lean_unsigned_to_nat(4u);
v___x_790_ = lean_nat_mul(v_size_x27_786_, v___x_789_);
v___x_791_ = lean_unsigned_to_nat(3u);
v___x_792_ = lean_nat_div(v___x_790_, v___x_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_array_get_size(v_buckets_x27_788_);
v___x_794_ = lean_nat_dec_le(v___x_792_, v___x_793_);
lean_dec(v___x_792_);
if (v___x_794_ == 0)
{
lean_object* v_val_795_; lean_object* v___x_797_; 
v_val_795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_788_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_val_795_);
lean_ctor_set(v___x_783_, 0, v_size_x27_786_);
v___x_797_ = v___x_783_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_size_x27_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_val_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v___x_800_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v_buckets_x27_788_);
lean_ctor_set(v___x_783_, 0, v_size_x27_786_);
v___x_800_ = v___x_783_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_size_x27_786_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_buckets_x27_788_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_dec(v_b_763_);
lean_dec(v_a_762_);
return v_m_761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_818_, lean_object* v_isTarget_819_, lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref(v_isTarget_819_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_b_823_);
return v___x_830_;
}
else
{
lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_912_; 
v_snd_831_ = lean_ctor_get(v_b_823_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_b_823_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v_b_823_, 0);
lean_dec(v_unused_913_);
v___x_833_ = v_b_823_;
v_isShared_834_ = v_isSharedCheck_912_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_dec(v_b_823_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_912_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_snd_835_; lean_object* v_fst_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_911_; 
v_snd_835_ = lean_ctor_get(v_snd_831_, 1);
v_fst_836_ = lean_ctor_get(v_snd_831_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_snd_831_);
if (v_isSharedCheck_911_ == 0)
{
v___x_838_ = v_snd_831_;
v_isShared_839_ = v_isSharedCheck_911_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_835_);
lean_inc(v_fst_836_);
lean_dec(v_snd_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_911_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_910_; 
v_fst_840_ = lean_ctor_get(v_snd_835_, 0);
v_snd_841_ = lean_ctor_get(v_snd_835_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_910_ == 0)
{
v___x_843_ = v_snd_835_;
v_isShared_844_ = v_isSharedCheck_910_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_840_);
lean_dec(v_snd_835_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_910_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v_a_847_; lean_object* v_a_854_; lean_object* v___x_855_; 
v___x_845_ = lean_box(0);
v_a_854_ = lean_array_uget_borrowed(v_as_820_, v_i_822_);
lean_inc(v_a_854_);
v___x_855_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_818_, v_a_854_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; uint8_t v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; 
lean_dec(v_a_856_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_snd_841_);
lean_ctor_set(v___x_838_, 0, v_fst_840_);
v___x_859_ = v___x_838_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_snd_841_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_859_);
lean_ctor_set(v___x_833_, 0, v_fst_836_);
v___x_861_ = v___x_833_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_847_ = v___x_861_;
goto v___jp_846_;
}
}
}
else
{
lean_object* v___x_864_; 
lean_inc_ref(v_isTarget_819_);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v_a_856_);
v___x_864_ = lean_apply_6(v_isTarget_819_, v_a_856_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, lean_box(0));
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; uint8_t v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_a_856_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_snd_841_);
lean_ctor_set(v___x_838_, 0, v_fst_840_);
v___x_868_ = v___x_838_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_841_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_868_);
lean_ctor_set(v___x_833_, 0, v_fst_836_);
v___x_870_ = v___x_833_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
v_a_847_ = v___x_870_;
goto v___jp_846_;
}
}
}
else
{
lean_object* v_self_873_; lean_object* v___x_874_; 
v_self_873_ = lean_ctor_get(v_a_856_, 0);
lean_inc_ref(v_self_873_);
lean_dec(v_a_856_);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_841_, v_self_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_875_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_818_, v_snd_841_, v_self_873_, v_fst_840_, v_fst_836_);
lean_inc_n(v___x_875_, 2);
v___x_876_ = l_Rat_ofInt(v___x_875_);
v___x_877_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_818_, v_self_873_, v___x_876_, v_snd_841_);
v___x_878_ = lean_box(0);
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_840_, v___x_875_, v___x_878_);
v___x_880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_881_ = lean_int_add(v___x_875_, v___x_880_);
lean_dec(v___x_875_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_877_);
lean_ctor_set(v___x_838_, 0, v___x_879_);
v___x_883_ = v___x_838_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_877_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_883_);
lean_ctor_set(v___x_833_, 0, v___x_881_);
v___x_885_ = v___x_833_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
v_a_847_ = v___x_885_;
goto v___jp_846_;
}
}
}
else
{
lean_object* v___x_889_; 
lean_dec_ref_known(v___x_874_, 1);
lean_dec_ref(v_self_873_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_snd_841_);
lean_ctor_set(v___x_838_, 0, v_fst_840_);
v___x_889_ = v___x_838_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_snd_841_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_889_);
lean_ctor_set(v___x_833_, 0, v_fst_836_);
v___x_891_ = v___x_833_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_847_ = v___x_891_;
goto v___jp_846_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_a_856_);
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_fst_840_);
lean_del_object(v___x_838_);
lean_dec(v_fst_836_);
lean_del_object(v___x_833_);
lean_dec_ref(v_isTarget_819_);
v_a_894_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_864_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_864_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_fst_840_);
lean_del_object(v___x_838_);
lean_dec(v_fst_836_);
lean_del_object(v___x_833_);
lean_dec_ref(v_isTarget_819_);
v_a_902_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_855_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_855_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
v___jp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_a_847_);
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_849_ = v___x_843_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_a_847_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
size_t v___x_850_; size_t v___x_851_; 
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_822_, v___x_850_);
v_i_822_ = v___x_851_;
v_b_823_ = v___x_849_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_914_, lean_object* v_isTarget_915_, lean_object* v_as_916_, lean_object* v_sz_917_, lean_object* v_i_918_, lean_object* v_b_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
size_t v_sz_boxed_925_; size_t v_i_boxed_926_; lean_object* v_res_927_; 
v_sz_boxed_925_ = lean_unbox_usize(v_sz_917_);
lean_dec(v_sz_917_);
v_i_boxed_926_ = lean_unbox_usize(v_i_918_);
lean_dec(v_i_918_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_914_, v_isTarget_915_, v_as_916_, v_sz_boxed_925_, v_i_boxed_926_, v_b_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v_as_916_);
lean_dec_ref(v_goal_914_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_928_, lean_object* v_isTarget_929_, lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec_ref(v_isTarget_929_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_933_);
return v___x_940_;
}
else
{
lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_1022_; 
v_snd_941_ = lean_ctor_get(v_b_933_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_b_933_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_b_933_, 0);
lean_dec(v_unused_1023_);
v___x_943_ = v_b_933_;
v_isShared_944_ = v_isSharedCheck_1022_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_dec(v_b_933_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_1022_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_snd_945_; lean_object* v_fst_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1021_; 
v_snd_945_ = lean_ctor_get(v_snd_941_, 1);
v_fst_946_ = lean_ctor_get(v_snd_941_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_snd_941_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_948_ = v_snd_941_;
v_isShared_949_ = v_isSharedCheck_1021_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_946_);
lean_dec(v_snd_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1021_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1020_; 
v_fst_950_ = lean_ctor_get(v_snd_945_, 0);
v_snd_951_ = lean_ctor_get(v_snd_945_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_snd_945_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_953_ = v_snd_945_;
v_isShared_954_ = v_isSharedCheck_1020_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_snd_945_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1020_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_a_957_; lean_object* v_a_964_; lean_object* v___x_965_; 
v___x_955_ = lean_box(0);
v_a_964_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
lean_inc(v_a_964_);
v___x_965_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_928_, v_a_964_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; uint8_t v___x_967_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v___x_965_, 1);
v___x_967_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_969_; 
lean_dec(v_a_966_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_969_ = v___x_948_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_snd_951_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_969_);
lean_ctor_set(v___x_943_, 0, v_fst_946_);
v___x_971_ = v___x_943_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
v_a_957_ = v___x_971_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_974_; 
lean_inc_ref(v_isTarget_929_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v_a_966_);
v___x_974_ = lean_apply_6(v_isTarget_929_, v_a_966_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; uint8_t v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = lean_unbox(v_a_975_);
lean_dec(v_a_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v_a_966_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_978_ = v___x_948_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_snd_951_);
v___x_978_ = v_reuseFailAlloc_982_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_978_);
lean_ctor_set(v___x_943_, 0, v_fst_946_);
v___x_980_ = v___x_943_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
v_a_957_ = v___x_980_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v_self_983_; lean_object* v___x_984_; 
v_self_983_ = lean_ctor_get(v_a_966_, 0);
lean_inc_ref(v_self_983_);
lean_dec(v_a_966_);
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_951_, v_self_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_985_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_928_, v_snd_951_, v_self_983_, v_fst_950_, v_fst_946_);
lean_inc_n(v___x_985_, 2);
v___x_986_ = l_Rat_ofInt(v___x_985_);
v___x_987_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_928_, v_self_983_, v___x_986_, v_snd_951_);
v___x_988_ = lean_box(0);
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_950_, v___x_985_, v___x_988_);
v___x_990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_991_ = lean_int_add(v___x_985_, v___x_990_);
lean_dec(v___x_985_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_987_);
lean_ctor_set(v___x_948_, 0, v___x_989_);
v___x_993_ = v___x_948_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_987_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_993_);
lean_ctor_set(v___x_943_, 0, v___x_991_);
v___x_995_ = v___x_943_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
v_a_957_ = v___x_995_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_999_; 
lean_dec_ref_known(v___x_984_, 1);
lean_dec_ref(v_self_983_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_999_ = v___x_948_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_snd_951_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_999_);
lean_ctor_set(v___x_943_, 0, v_fst_946_);
v___x_1001_ = v___x_943_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
v_a_957_ = v___x_1001_;
goto v___jp_956_;
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_966_);
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_del_object(v___x_943_);
lean_dec_ref(v_isTarget_929_);
v_a_1004_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_974_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_974_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_del_object(v___x_943_);
lean_dec_ref(v_isTarget_929_);
v_a_1012_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_965_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_965_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
v___jp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_a_957_);
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_a_957_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_932_, v___x_960_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_928_, v_isTarget_929_, v_as_930_, v_sz_931_, v___x_961_, v___x_959_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_962_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1024_, lean_object* v_isTarget_1025_, lean_object* v_as_1026_, lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1024_, v_isTarget_1025_, v_as_1026_, v_sz_boxed_1035_, v_i_boxed_1036_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v_as_1026_);
lean_dec_ref(v_goal_1024_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1038_, lean_object* v_isTarget_1039_, lean_object* v_as_1040_, size_t v_sz_1041_, size_t v_i_1042_, lean_object* v_b_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_usize_dec_lt(v_i_1042_, v_sz_1041_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec_ref(v_isTarget_1039_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_b_1043_);
return v___x_1050_;
}
else
{
lean_object* v_snd_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1132_; 
v_snd_1051_ = lean_ctor_get(v_b_1043_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_b_1043_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_b_1043_, 0);
lean_dec(v_unused_1133_);
v___x_1053_ = v_b_1043_;
v_isShared_1054_ = v_isSharedCheck_1132_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snd_1051_);
lean_dec(v_b_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1132_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_snd_1055_; lean_object* v_fst_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1131_; 
v_snd_1055_ = lean_ctor_get(v_snd_1051_, 1);
v_fst_1056_ = lean_ctor_get(v_snd_1051_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_snd_1051_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1058_ = v_snd_1051_;
v_isShared_1059_ = v_isSharedCheck_1131_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_snd_1055_);
lean_inc(v_fst_1056_);
lean_dec(v_snd_1051_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1131_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1130_; 
v_fst_1060_ = lean_ctor_get(v_snd_1055_, 0);
v_snd_1061_ = lean_ctor_get(v_snd_1055_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_snd_1055_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1063_ = v_snd_1055_;
v_isShared_1064_ = v_isSharedCheck_1130_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1061_);
lean_inc(v_fst_1060_);
lean_dec(v_snd_1055_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1130_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v_a_1067_; lean_object* v_a_1074_; lean_object* v___x_1075_; 
v___x_1065_ = lean_box(0);
v_a_1074_ = lean_array_uget_borrowed(v_as_1040_, v_i_1042_);
lean_inc(v_a_1074_);
v___x_1075_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1038_, v_a_1074_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; uint8_t v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_a_1076_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1079_ = v___x_1058_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_snd_1061_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1079_);
lean_ctor_set(v___x_1053_, 0, v_fst_1056_);
v___x_1081_ = v___x_1053_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v_a_1067_ = v___x_1081_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v___x_1084_; 
lean_inc_ref(v_isTarget_1039_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v_a_1076_);
v___x_1084_ = lean_apply_6(v_isTarget_1039_, v_a_1076_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_a_1076_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1088_ = v___x_1058_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_snd_1061_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1088_);
lean_ctor_set(v___x_1053_, 0, v_fst_1056_);
v___x_1090_ = v___x_1053_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v_a_1067_ = v___x_1090_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v_self_1093_; lean_object* v___x_1094_; 
v_self_1093_ = lean_ctor_get(v_a_1076_, 0);
lean_inc_ref(v_self_1093_);
lean_dec(v_a_1076_);
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1061_, v_self_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1095_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1038_, v_snd_1061_, v_self_1093_, v_fst_1060_, v_fst_1056_);
lean_inc_n(v___x_1095_, 2);
v___x_1096_ = l_Rat_ofInt(v___x_1095_);
v___x_1097_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1038_, v_self_1093_, v___x_1096_, v_snd_1061_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1060_, v___x_1095_, v___x_1098_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1101_ = lean_int_add(v___x_1095_, v___x_1100_);
lean_dec(v___x_1095_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1097_);
lean_ctor_set(v___x_1058_, 0, v___x_1099_);
v___x_1103_ = v___x_1058_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1097_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1103_);
lean_ctor_set(v___x_1053_, 0, v___x_1101_);
v___x_1105_ = v___x_1053_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v_a_1067_ = v___x_1105_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_dec_ref_known(v___x_1094_, 1);
lean_dec_ref(v_self_1093_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1109_ = v___x_1058_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_snd_1061_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1109_);
lean_ctor_set(v___x_1053_, 0, v_fst_1056_);
v___x_1111_ = v___x_1053_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_a_1067_ = v___x_1111_;
goto v___jp_1066_;
}
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_a_1076_);
lean_del_object(v___x_1063_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_del_object(v___x_1058_);
lean_dec(v_fst_1056_);
lean_del_object(v___x_1053_);
lean_dec_ref(v_isTarget_1039_);
v_a_1114_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1084_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1084_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1063_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_del_object(v___x_1058_);
lean_dec(v_fst_1056_);
lean_del_object(v___x_1053_);
lean_dec_ref(v_isTarget_1039_);
v_a_1122_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1075_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1075_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v_a_1067_);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_a_1067_);
v___x_1069_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
size_t v___x_1070_; size_t v___x_1071_; 
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1042_, v___x_1070_);
v_i_1042_ = v___x_1071_;
v_b_1043_ = v___x_1069_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1134_, lean_object* v_isTarget_1135_, lean_object* v_as_1136_, lean_object* v_sz_1137_, lean_object* v_i_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
size_t v_sz_boxed_1145_; size_t v_i_boxed_1146_; lean_object* v_res_1147_; 
v_sz_boxed_1145_ = lean_unbox_usize(v_sz_1137_);
lean_dec(v_sz_1137_);
v_i_boxed_1146_ = lean_unbox_usize(v_i_1138_);
lean_dec(v_i_1138_);
v_res_1147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1134_, v_isTarget_1135_, v_as_1136_, v_sz_boxed_1145_, v_i_boxed_1146_, v_b_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_as_1136_);
lean_dec_ref(v_goal_1134_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1148_, lean_object* v_isTarget_1149_, lean_object* v_as_1150_, size_t v_sz_1151_, size_t v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1152_, v_sz_1151_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec_ref(v_isTarget_1149_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1153_);
return v___x_1160_;
}
else
{
lean_object* v_snd_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1242_; 
v_snd_1161_ = lean_ctor_get(v_b_1153_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_b_1153_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_b_1153_, 0);
lean_dec(v_unused_1243_);
v___x_1163_ = v_b_1153_;
v_isShared_1164_ = v_isSharedCheck_1242_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snd_1161_);
lean_dec(v_b_1153_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1242_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_snd_1165_; lean_object* v_fst_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1241_; 
v_snd_1165_ = lean_ctor_get(v_snd_1161_, 1);
v_fst_1166_ = lean_ctor_get(v_snd_1161_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_snd_1161_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1168_ = v_snd_1161_;
v_isShared_1169_ = v_isSharedCheck_1241_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1165_);
lean_inc(v_fst_1166_);
lean_dec(v_snd_1161_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1241_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1240_; 
v_fst_1170_ = lean_ctor_get(v_snd_1165_, 0);
v_snd_1171_ = lean_ctor_get(v_snd_1165_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_snd_1165_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1173_ = v_snd_1165_;
v_isShared_1174_ = v_isSharedCheck_1240_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_snd_1165_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1240_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v_a_1177_; lean_object* v_a_1184_; lean_object* v___x_1185_; 
v___x_1175_ = lean_box(0);
v_a_1184_ = lean_array_uget_borrowed(v_as_1150_, v_i_1152_);
lean_inc(v_a_1184_);
v___x_1185_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1148_, v_a_1184_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; uint8_t v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1189_; 
lean_dec(v_a_1186_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_snd_1171_);
lean_ctor_set(v___x_1168_, 0, v_fst_1170_);
v___x_1189_ = v___x_1168_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_snd_1171_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1189_);
lean_ctor_set(v___x_1163_, 0, v_fst_1166_);
v___x_1191_ = v___x_1163_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_a_1177_ = v___x_1191_;
goto v___jp_1176_;
}
}
}
else
{
lean_object* v___x_1194_; 
lean_inc_ref(v_isTarget_1149_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v_a_1186_);
v___x_1194_ = lean_apply_6(v_isTarget_1149_, v_a_1186_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, lean_box(0));
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; uint8_t v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1198_; 
lean_dec(v_a_1186_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_snd_1171_);
lean_ctor_set(v___x_1168_, 0, v_fst_1170_);
v___x_1198_ = v___x_1168_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_snd_1171_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1198_);
lean_ctor_set(v___x_1163_, 0, v_fst_1166_);
v___x_1200_ = v___x_1163_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v_a_1177_ = v___x_1200_;
goto v___jp_1176_;
}
}
}
else
{
lean_object* v_self_1203_; lean_object* v___x_1204_; 
v_self_1203_ = lean_ctor_get(v_a_1186_, 0);
lean_inc_ref(v_self_1203_);
lean_dec(v_a_1186_);
v___x_1204_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1171_, v_self_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1205_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1148_, v_snd_1171_, v_self_1203_, v_fst_1170_, v_fst_1166_);
lean_inc_n(v___x_1205_, 2);
v___x_1206_ = l_Rat_ofInt(v___x_1205_);
v___x_1207_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1148_, v_self_1203_, v___x_1206_, v_snd_1171_);
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1170_, v___x_1205_, v___x_1208_);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1211_ = lean_int_add(v___x_1205_, v___x_1210_);
lean_dec(v___x_1205_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1207_);
lean_ctor_set(v___x_1168_, 0, v___x_1209_);
v___x_1213_ = v___x_1168_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1207_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1213_);
lean_ctor_set(v___x_1163_, 0, v___x_1211_);
v___x_1215_ = v___x_1163_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
v_a_1177_ = v___x_1215_;
goto v___jp_1176_;
}
}
}
else
{
lean_object* v___x_1219_; 
lean_dec_ref_known(v___x_1204_, 1);
lean_dec_ref(v_self_1203_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_snd_1171_);
lean_ctor_set(v___x_1168_, 0, v_fst_1170_);
v___x_1219_ = v___x_1168_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_snd_1171_);
v___x_1219_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1219_);
lean_ctor_set(v___x_1163_, 0, v_fst_1166_);
v___x_1221_ = v___x_1163_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_a_1177_ = v___x_1221_;
goto v___jp_1176_;
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1186_);
lean_del_object(v___x_1173_);
lean_dec(v_snd_1171_);
lean_dec(v_fst_1170_);
lean_del_object(v___x_1168_);
lean_dec(v_fst_1166_);
lean_del_object(v___x_1163_);
lean_dec_ref(v_isTarget_1149_);
v_a_1224_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1194_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1194_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_del_object(v___x_1173_);
lean_dec(v_snd_1171_);
lean_dec(v_fst_1170_);
lean_del_object(v___x_1168_);
lean_dec(v_fst_1166_);
lean_del_object(v___x_1163_);
lean_dec_ref(v_isTarget_1149_);
v_a_1232_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1185_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1185_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_a_1177_);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_a_1177_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1152_, v___x_1180_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1148_, v_isTarget_1149_, v_as_1150_, v_sz_1151_, v___x_1181_, v___x_1179_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1182_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1244_, lean_object* v_isTarget_1245_, lean_object* v_as_1246_, lean_object* v_sz_1247_, lean_object* v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
size_t v_sz_boxed_1255_; size_t v_i_boxed_1256_; lean_object* v_res_1257_; 
v_sz_boxed_1255_ = lean_unbox_usize(v_sz_1247_);
lean_dec(v_sz_1247_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1248_);
lean_dec(v_i_1248_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1244_, v_isTarget_1245_, v_as_1246_, v_sz_boxed_1255_, v_i_boxed_1256_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_as_1246_);
lean_dec_ref(v_goal_1244_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1258_, lean_object* v_goal_1259_, lean_object* v_isTarget_1260_, lean_object* v_n_1261_, lean_object* v_b_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
if (lean_obj_tag(v_n_1261_) == 0)
{
lean_object* v_cs_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; size_t v_sz_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v_cs_1268_ = lean_ctor_get(v_n_1261_, 0);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_b_1262_);
v_sz_1271_ = lean_array_size(v_cs_1268_);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1258_, v_goal_1259_, v_isTarget_1260_, v_cs_1268_, v_sz_1271_, v___x_1272_, v___x_1270_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1288_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_fst_1278_; 
v_fst_1278_ = lean_ctor_get(v_a_1274_, 0);
if (lean_obj_tag(v_fst_1278_) == 0)
{
lean_object* v_snd_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v_snd_1279_ = lean_ctor_get(v_a_1274_, 1);
lean_inc(v_snd_1279_);
lean_dec(v_a_1274_);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_snd_1279_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1280_);
v___x_1282_ = v___x_1276_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1286_; 
lean_inc_ref(v_fst_1278_);
lean_dec(v_a_1274_);
v_val_1284_ = lean_ctor_get(v_fst_1278_, 0);
lean_inc(v_val_1284_);
lean_dec_ref_known(v_fst_1278_, 1);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_val_1284_);
v___x_1286_ = v___x_1276_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_val_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1273_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1273_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_vs_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; size_t v_sz_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v_vs_1297_ = lean_ctor_get(v_n_1261_, 0);
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_b_1262_);
v_sz_1300_ = lean_array_size(v_vs_1297_);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1259_, v_isTarget_1260_, v_vs_1297_, v_sz_1300_, v___x_1301_, v___x_1299_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1317_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1317_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1317_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_fst_1307_; 
v_fst_1307_ = lean_ctor_get(v_a_1303_, 0);
if (lean_obj_tag(v_fst_1307_) == 0)
{
lean_object* v_snd_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v_snd_1308_ = lean_ctor_get(v_a_1303_, 1);
lean_inc(v_snd_1308_);
lean_dec(v_a_1303_);
v___x_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_snd_1308_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1309_);
v___x_1311_ = v___x_1305_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1315_; 
lean_inc_ref(v_fst_1307_);
lean_dec(v_a_1303_);
v_val_1313_ = lean_ctor_get(v_fst_1307_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v_fst_1307_, 1);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v_val_1313_);
v___x_1315_ = v___x_1305_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_val_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1302_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1302_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1326_, lean_object* v_goal_1327_, lean_object* v_isTarget_1328_, lean_object* v_as_1329_, size_t v_sz_1330_, size_t v_i_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v___x_1338_; 
v___x_1338_ = lean_usize_dec_lt(v_i_1331_, v_sz_1330_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_isTarget_1328_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1332_);
return v___x_1339_;
}
else
{
lean_object* v_snd_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1374_; 
v_snd_1340_ = lean_ctor_get(v_b_1332_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_b_1332_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_b_1332_, 0);
lean_dec(v_unused_1375_);
v___x_1342_ = v_b_1332_;
v_isShared_1343_ = v_isSharedCheck_1374_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1340_);
lean_dec(v_b_1332_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1374_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v_a_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v_a_1345_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
lean_inc(v_snd_1340_);
lean_inc_ref(v_isTarget_1328_);
v___x_1346_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1326_, v_goal_1327_, v_isTarget_1328_, v_a_1345_, v_snd_1340_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1365_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1365_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec_ref(v_isTarget_1328_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_a_1347_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1351_);
v___x_1353_ = v___x_1342_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1340_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; 
lean_del_object(v___x_1349_);
lean_dec(v_snd_1340_);
v_a_1358_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_a_1347_, 1);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_a_1358_);
lean_ctor_set(v___x_1342_, 0, v___x_1344_);
v___x_1360_ = v___x_1342_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1358_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
size_t v___x_1361_; size_t v___x_1362_; 
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_add(v_i_1331_, v___x_1361_);
v_i_1331_ = v___x_1362_;
v_b_1332_ = v___x_1360_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_del_object(v___x_1342_);
lean_dec(v_snd_1340_);
lean_dec_ref(v_isTarget_1328_);
v_a_1366_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1346_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1346_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1376_, lean_object* v_goal_1377_, lean_object* v_isTarget_1378_, lean_object* v_as_1379_, lean_object* v_sz_1380_, lean_object* v_i_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
size_t v_sz_boxed_1388_; size_t v_i_boxed_1389_; lean_object* v_res_1390_; 
v_sz_boxed_1388_ = lean_unbox_usize(v_sz_1380_);
lean_dec(v_sz_1380_);
v_i_boxed_1389_ = lean_unbox_usize(v_i_1381_);
lean_dec(v_i_1381_);
v_res_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1376_, v_goal_1377_, v_isTarget_1378_, v_as_1379_, v_sz_boxed_1388_, v_i_boxed_1389_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v_as_1379_);
lean_dec_ref(v_goal_1377_);
lean_dec_ref(v_init_1376_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1391_, lean_object* v_goal_1392_, lean_object* v_isTarget_1393_, lean_object* v_n_1394_, lean_object* v_b_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1391_, v_goal_1392_, v_isTarget_1393_, v_n_1394_, v_b_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec_ref(v_n_1394_);
lean_dec_ref(v_goal_1392_);
lean_dec_ref(v_init_1391_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1402_, lean_object* v_isTarget_1403_, lean_object* v_t_1404_, lean_object* v_init_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_root_1411_; lean_object* v_tail_1412_; lean_object* v___x_1413_; 
v_root_1411_ = lean_ctor_get(v_t_1404_, 0);
v_tail_1412_ = lean_ctor_get(v_t_1404_, 1);
lean_inc_ref(v_isTarget_1403_);
lean_inc_ref(v_init_1405_);
v___x_1413_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1405_, v_goal_1402_, v_isTarget_1403_, v_root_1411_, v_init_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec_ref(v_init_1405_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1450_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1450_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1450_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
if (lean_obj_tag(v_a_1414_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; 
lean_dec_ref(v_isTarget_1403_);
v_a_1418_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v_a_1414_, 1);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_a_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; size_t v_sz_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
lean_del_object(v___x_1416_);
v_a_1422_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v_a_1414_, 1);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_a_1422_);
v_sz_1425_ = lean_array_size(v_tail_1412_);
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1402_, v_isTarget_1403_, v_tail_1412_, v_sz_1425_, v___x_1426_, v___x_1424_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1441_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1441_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1441_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; 
v_fst_1432_ = lean_ctor_get(v_a_1428_, 0);
if (lean_obj_tag(v_fst_1432_) == 0)
{
lean_object* v_snd_1433_; lean_object* v___x_1435_; 
v_snd_1433_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1433_);
lean_dec(v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_snd_1433_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_snd_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
lean_object* v_val_1437_; lean_object* v___x_1439_; 
lean_inc_ref(v_fst_1432_);
lean_dec(v_a_1428_);
v_val_1437_ = lean_ctor_get(v_fst_1432_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v_fst_1432_, 1);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_val_1437_);
v___x_1439_ = v___x_1430_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_val_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1427_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1427_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_isTarget_1403_);
v_a_1451_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1413_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1413_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1459_, lean_object* v_isTarget_1460_, lean_object* v_t_1461_, lean_object* v_init_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1459_, v_isTarget_1460_, v_t_1461_, v_init_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_t_1461_);
lean_dec_ref(v_goal_1459_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1470_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
else
{
lean_object* v_value_1474_; lean_object* v_tail_1475_; lean_object* v_num_1476_; lean_object* v_den_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_value_1474_ = lean_ctor_get(v_a_1469_, 1);
lean_inc(v_value_1474_);
v_tail_1475_ = lean_ctor_get(v_a_1469_, 2);
lean_inc(v_tail_1475_);
lean_dec_ref_known(v_a_1469_, 3);
v_num_1476_ = lean_ctor_get(v_value_1474_, 0);
lean_inc(v_num_1476_);
v_den_1477_ = lean_ctor_get(v_value_1474_, 1);
lean_inc(v_den_1477_);
lean_dec(v_value_1474_);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_dec_eq(v_den_1477_, v___x_1478_);
lean_dec(v_den_1477_);
if (v___x_1479_ == 0)
{
lean_dec(v_num_1476_);
v_a_1469_ = v_tail_1475_;
goto _start;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_box(0);
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1470_, v_num_1476_, v___x_1481_);
v_a_1469_ = v_tail_1475_;
v_a_1470_ = v___x_1482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1484_, v_a_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1488_, size_t v_sz_1489_, size_t v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_lt(v_i_1490_, v_sz_1489_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_b_1491_);
return v___x_1498_;
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_array_uget_borrowed(v_as_1488_, v_i_1490_);
lean_inc(v_a_1499_);
v___x_1500_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1499_, v_b_1491_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1513_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1513_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
if (lean_obj_tag(v_a_1501_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; 
v_a_1505_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v_a_1501_, 1);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v_a_1505_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
else
{
lean_object* v_a_1509_; size_t v___x_1510_; size_t v___x_1511_; 
lean_del_object(v___x_1503_);
v_a_1509_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_a_1501_, 1);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1490_, v___x_1510_);
v_i_1490_ = v___x_1511_;
v_b_1491_ = v_a_1509_;
goto _start;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1500_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1500_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1522_, lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
size_t v_sz_boxed_1531_; size_t v_i_boxed_1532_; lean_object* v_res_1533_; 
v_sz_boxed_1531_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1532_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1522_, v_sz_boxed_1531_, v_i_boxed_1532_, v_b_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_as_1522_);
return v_res_1533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_unsigned_to_nat(16u);
v___x_1536_ = lean_mk_array(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_used_1539_; 
v___x_1537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1538_ = lean_unsigned_to_nat(0u);
v_used_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1539_, 0, v___x_1538_);
lean_ctor_set(v_used_1539_, 1, v___x_1537_);
return v_used_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1540_, lean_object* v_isTarget_1541_, lean_object* v_model_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_buckets_1548_; lean_object* v_nextVal_1549_; lean_object* v_used_1550_; size_t v_sz_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v_buckets_1548_ = lean_ctor_get(v_model_1542_, 1);
v_nextVal_1549_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_used_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1551_ = lean_array_size(v_buckets_1548_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1548_, v_sz_1551_, v___x_1552_, v_used_1550_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_toGoalState_1554_; lean_object* v_a_1555_; lean_object* v_exprs_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_toGoalState_1554_ = lean_ctor_get(v_goal_1540_, 0);
v_a_1555_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 1);
v_exprs_1556_ = lean_ctor_get(v_toGoalState_1554_, 2);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_a_1555_);
lean_ctor_set(v___x_1557_, 1, v_model_1542_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_nextVal_1549_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1540_, v_isTarget_1541_, v_exprs_1556_, v___x_1558_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1569_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_snd_1564_; lean_object* v_snd_1565_; lean_object* v___x_1567_; 
v_snd_1564_ = lean_ctor_get(v_a_1560_, 1);
lean_inc(v_snd_1564_);
lean_dec(v_a_1560_);
v_snd_1565_ = lean_ctor_get(v_snd_1564_, 1);
lean_inc(v_snd_1565_);
lean_dec(v_snd_1564_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v_snd_1565_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_snd_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1559_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1559_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v_model_1542_);
lean_dec_ref(v_isTarget_1541_);
v_a_1578_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1553_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1553_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1586_, lean_object* v_isTarget_1587_, lean_object* v_model_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1586_, v_isTarget_1587_, v_model_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec_ref(v_goal_1586_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1595_, lean_object* v_m_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1596_, v_a_1597_, v_b_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1600_, v_a_1601_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1608_, v_a_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1616_, lean_object* v_data_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1619_, lean_object* v_i_1620_, lean_object* v_source_1621_, lean_object* v_target_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1620_, v_source_1621_, v_target_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1628_, lean_object* v_hi_1629_, lean_object* v_pivot_1630_, lean_object* v_as_1631_, lean_object* v_i_1632_, lean_object* v_k_1633_){
_start:
{
uint8_t v___y_1635_; uint8_t v___x_1644_; 
v___x_1644_ = lean_nat_dec_lt(v_k_1633_, v_hi_1629_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_k_1633_);
v___x_1645_ = lean_array_fswap(v_as_1631_, v_i_1632_, v_hi_1629_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_i_1632_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; lean_object* v_fst_1648_; lean_object* v_fst_1649_; lean_object* v_g_u2081_1650_; lean_object* v_g_u2082_1651_; uint8_t v___x_1652_; 
v___x_1647_ = lean_array_fget_borrowed(v_as_1631_, v_k_1633_);
v_fst_1648_ = lean_ctor_get(v___x_1647_, 0);
v_fst_1649_ = lean_ctor_get(v_pivot_1630_, 0);
v_g_u2081_1650_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1628_, v_fst_1648_);
v_g_u2082_1651_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1628_, v_fst_1649_);
v___x_1652_ = lean_nat_dec_eq(v_g_u2081_1650_, v_g_u2082_1651_);
if (v___x_1652_ == 0)
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_nat_dec_lt(v_g_u2081_1650_, v_g_u2082_1651_);
lean_dec(v_g_u2082_1651_);
lean_dec(v_g_u2081_1650_);
v___y_1635_ = v___x_1653_;
goto v___jp_1634_;
}
else
{
uint8_t v___x_1654_; 
lean_dec(v_g_u2082_1651_);
lean_dec(v_g_u2081_1650_);
v___x_1654_ = lean_expr_lt(v_fst_1648_, v_fst_1649_);
v___y_1635_ = v___x_1654_;
goto v___jp_1634_;
}
}
v___jp_1634_:
{
if (v___y_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_k_1633_, v___x_1636_);
lean_dec(v_k_1633_);
v_k_1633_ = v___x_1637_;
goto _start;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_array_fswap(v_as_1631_, v_i_1632_, v_k_1633_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_nat_add(v_i_1632_, v___x_1640_);
lean_dec(v_i_1632_);
v___x_1642_ = lean_nat_add(v_k_1633_, v___x_1640_);
lean_dec(v_k_1633_);
v_as_1631_ = v___x_1639_;
v_i_1632_ = v___x_1641_;
v_k_1633_ = v___x_1642_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1655_, lean_object* v_hi_1656_, lean_object* v_pivot_1657_, lean_object* v_as_1658_, lean_object* v_i_1659_, lean_object* v_k_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1655_, v_hi_1656_, v_pivot_1657_, v_as_1658_, v_i_1659_, v_k_1660_);
lean_dec_ref(v_pivot_1657_);
lean_dec(v_hi_1656_);
lean_dec_ref(v_goal_1655_);
return v_res_1661_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v_fst_1665_; lean_object* v_fst_1666_; lean_object* v_g_u2081_1667_; lean_object* v_g_u2082_1668_; uint8_t v___x_1669_; 
v_fst_1665_ = lean_ctor_get(v_x_1663_, 0);
v_fst_1666_ = lean_ctor_get(v_x_1664_, 0);
v_g_u2081_1667_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1662_, v_fst_1665_);
v_g_u2082_1668_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1662_, v_fst_1666_);
v___x_1669_ = lean_nat_dec_eq(v_g_u2081_1667_, v_g_u2082_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_nat_dec_lt(v_g_u2081_1667_, v_g_u2082_1668_);
lean_dec(v_g_u2082_1668_);
lean_dec(v_g_u2081_1667_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; 
lean_dec(v_g_u2082_1668_);
lean_dec(v_g_u2081_1667_);
v___x_1671_ = lean_expr_lt(v_fst_1665_, v_fst_1666_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
uint8_t v_res_1675_; lean_object* v_r_1676_; 
v_res_1675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1672_, v_x_1673_, v_x_1674_);
lean_dec_ref(v_x_1674_);
lean_dec_ref(v_x_1673_);
lean_dec_ref(v_goal_1672_);
v_r_1676_ = lean_box(v_res_1675_);
return v_r_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1677_, lean_object* v_n_1678_, lean_object* v_as_1679_, lean_object* v_lo_1680_, lean_object* v_hi_1681_){
_start:
{
lean_object* v___y_1683_; uint8_t v___x_1693_; 
v___x_1693_ = lean_nat_dec_lt(v_lo_1680_, v_hi_1681_);
if (v___x_1693_ == 0)
{
lean_dec(v_lo_1680_);
return v_as_1679_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_mid_1696_; lean_object* v___y_1698_; lean_object* v___y_1704_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1694_ = lean_nat_add(v_lo_1680_, v_hi_1681_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v_mid_1696_ = lean_nat_shiftr(v___x_1694_, v___x_1695_);
lean_dec(v___x_1694_);
v___x_1709_ = lean_array_fget_borrowed(v_as_1679_, v_mid_1696_);
v___x_1710_ = lean_array_fget_borrowed(v_as_1679_, v_lo_1680_);
v___x_1711_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1677_, v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
v___y_1704_ = v_as_1679_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_array_fswap(v_as_1679_, v_lo_1680_, v_mid_1696_);
v___y_1704_ = v___x_1712_;
goto v___jp_1703_;
}
v___jp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1699_ = lean_array_fget_borrowed(v___y_1698_, v_mid_1696_);
v___x_1700_ = lean_array_fget_borrowed(v___y_1698_, v_hi_1681_);
v___x_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1677_, v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_dec(v_mid_1696_);
v___y_1683_ = v___y_1698_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_array_fswap(v___y_1698_, v_mid_1696_, v_hi_1681_);
lean_dec(v_mid_1696_);
v___y_1683_ = v___x_1702_;
goto v___jp_1682_;
}
}
v___jp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1705_ = lean_array_fget_borrowed(v___y_1704_, v_hi_1681_);
v___x_1706_ = lean_array_fget_borrowed(v___y_1704_, v_lo_1680_);
v___x_1707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1677_, v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
v___y_1698_ = v___y_1704_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_array_fswap(v___y_1704_, v_lo_1680_, v_hi_1681_);
v___y_1698_ = v___x_1708_;
goto v___jp_1697_;
}
}
}
v___jp_1682_:
{
lean_object* v_pivot_1684_; lean_object* v___x_1685_; lean_object* v_fst_1686_; lean_object* v_snd_1687_; uint8_t v___x_1688_; 
v_pivot_1684_ = lean_array_fget(v___y_1683_, v_hi_1681_);
lean_inc_n(v_lo_1680_, 2);
v___x_1685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1677_, v_hi_1681_, v_pivot_1684_, v___y_1683_, v_lo_1680_, v_lo_1680_);
lean_dec(v_pivot_1684_);
v_fst_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_fst_1686_);
v_snd_1687_ = lean_ctor_get(v___x_1685_, 1);
lean_inc(v_snd_1687_);
lean_dec_ref(v___x_1685_);
v___x_1688_ = lean_nat_dec_le(v_hi_1681_, v_fst_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1677_, v_n_1678_, v_snd_1687_, v_lo_1680_, v_fst_1686_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_nat_add(v_fst_1686_, v___x_1690_);
lean_dec(v_fst_1686_);
v_as_1679_ = v___x_1689_;
v_lo_1680_ = v___x_1691_;
goto _start;
}
else
{
lean_dec(v_fst_1686_);
lean_dec(v_lo_1680_);
return v_snd_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1713_, lean_object* v_n_1714_, lean_object* v_as_1715_, lean_object* v_lo_1716_, lean_object* v_hi_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1713_, v_n_1714_, v_as_1715_, v_lo_1716_, v_hi_1717_);
lean_dec(v_hi_1717_);
lean_dec(v_n_1714_);
lean_dec_ref(v_goal_1713_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1719_, lean_object* v_m_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = lean_array_get_size(v_m_1720_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_nat_dec_eq(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___y_1727_; uint8_t v___x_1731_; 
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_sub(v___x_1721_, v___x_1724_);
v___x_1731_ = lean_nat_dec_le(v___x_1722_, v___x_1725_);
if (v___x_1731_ == 0)
{
lean_inc(v___x_1725_);
v___y_1727_ = v___x_1725_;
goto v___jp_1726_;
}
else
{
v___y_1727_ = v___x_1722_;
goto v___jp_1726_;
}
v___jp_1726_:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_nat_dec_le(v___y_1727_, v___x_1725_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
lean_dec(v___x_1725_);
lean_inc(v___y_1727_);
v___x_1729_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1719_, v___x_1721_, v_m_1720_, v___y_1727_, v___y_1727_);
lean_dec(v___y_1727_);
return v___x_1729_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1719_, v___x_1721_, v_m_1720_, v___y_1727_, v___x_1725_);
lean_dec(v___x_1725_);
return v___x_1730_;
}
}
}
else
{
return v_m_1720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1732_, lean_object* v_m_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1732_, v_m_1733_);
lean_dec_ref(v_goal_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1735_, lean_object* v_n_1736_, lean_object* v_as_1737_, lean_object* v_lo_1738_, lean_object* v_hi_1739_, lean_object* v_w_1740_, lean_object* v_hlo_1741_, lean_object* v_hhi_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1735_, v_n_1736_, v_as_1737_, v_lo_1738_, v_hi_1739_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1744_, lean_object* v_n_1745_, lean_object* v_as_1746_, lean_object* v_lo_1747_, lean_object* v_hi_1748_, lean_object* v_w_1749_, lean_object* v_hlo_1750_, lean_object* v_hhi_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1744_, v_n_1745_, v_as_1746_, v_lo_1747_, v_hi_1748_, v_w_1749_, v_hlo_1750_, v_hhi_1751_);
lean_dec(v_hi_1748_);
lean_dec(v_n_1745_);
lean_dec_ref(v_goal_1744_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1753_, lean_object* v_n_1754_, lean_object* v_lo_1755_, lean_object* v_hi_1756_, lean_object* v_hhi_1757_, lean_object* v_pivot_1758_, lean_object* v_as_1759_, lean_object* v_i_1760_, lean_object* v_k_1761_, lean_object* v_ilo_1762_, lean_object* v_ik_1763_, lean_object* v_w_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1753_, v_hi_1756_, v_pivot_1758_, v_as_1759_, v_i_1760_, v_k_1761_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1766_, lean_object* v_n_1767_, lean_object* v_lo_1768_, lean_object* v_hi_1769_, lean_object* v_hhi_1770_, lean_object* v_pivot_1771_, lean_object* v_as_1772_, lean_object* v_i_1773_, lean_object* v_k_1774_, lean_object* v_ilo_1775_, lean_object* v_ik_1776_, lean_object* v_w_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1766_, v_n_1767_, v_lo_1768_, v_hi_1769_, v_hhi_1770_, v_pivot_1771_, v_as_1772_, v_i_1773_, v_k_1774_, v_ilo_1775_, v_ik_1776_, v_w_1777_);
lean_dec_ref(v_pivot_1771_);
lean_dec(v_hi_1769_);
lean_dec(v_lo_1768_);
lean_dec(v_n_1767_);
lean_dec_ref(v_goal_1766_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
if (lean_obj_tag(v_a_1779_) == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1780_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v_key_1784_; lean_object* v_value_1785_; lean_object* v_tail_1786_; uint8_t v___x_1787_; 
v_key_1784_ = lean_ctor_get(v_a_1779_, 0);
lean_inc_n(v_key_1784_, 2);
v_value_1785_ = lean_ctor_get(v_a_1779_, 1);
lean_inc(v_value_1785_);
v_tail_1786_ = lean_ctor_get(v_a_1779_, 2);
lean_inc(v_tail_1786_);
lean_dec_ref_known(v_a_1779_, 3);
v___x_1787_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1784_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_key_1784_);
lean_ctor_set(v___x_1788_, 1, v_value_1785_);
v___x_1789_ = lean_array_push(v_a_1780_, v___x_1788_);
v_a_1779_ = v_tail_1786_;
v_a_1780_ = v___x_1789_;
goto _start;
}
else
{
lean_dec(v_value_1785_);
lean_dec(v_key_1784_);
v_a_1779_ = v_tail_1786_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1792_, v_a_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1796_, size_t v_sz_1797_, size_t v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_usize_dec_lt(v_i_1798_, v_sz_1797_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_b_1799_);
return v___x_1806_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_array_uget_borrowed(v_as_1796_, v_i_1798_);
lean_inc(v_a_1807_);
v___x_1808_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1807_, v_b_1799_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1821_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1821_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1821_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v_a_1809_, 1);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_a_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v_a_1817_; size_t v___x_1818_; size_t v___x_1819_; 
lean_del_object(v___x_1811_);
v_a_1817_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v_a_1809_, 1);
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = lean_usize_add(v_i_1798_, v___x_1818_);
v_i_1798_ = v___x_1819_;
v_b_1799_ = v_a_1817_;
goto _start;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1808_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1808_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
size_t v_sz_boxed_1839_; size_t v_i_boxed_1840_; lean_object* v_res_1841_; 
v_sz_boxed_1839_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1840_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1830_, v_sz_boxed_1839_, v_i_boxed_1840_, v_b_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec_ref(v_as_1830_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1844_, lean_object* v_isTarget_1845_, lean_object* v_model_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1844_, v_isTarget_1845_, v_model_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_buckets_1854_; lean_object* v___x_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v_buckets_1854_ = lean_ctor_get(v_a_1853_, 1);
lean_inc_ref(v_buckets_1854_);
lean_dec(v_a_1853_);
v___x_1855_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1856_ = lean_array_size(v_buckets_1854_);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1854_, v_sz_1856_, v___x_1857_, v___x_1855_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec_ref(v_buckets_1854_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1844_, v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
return v___x_1858_;
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1852_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1852_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1876_, lean_object* v_isTarget_1877_, lean_object* v_model_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1876_, v_isTarget_1877_, v_model_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec_ref(v_goal_1876_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1885_, v_a_1886_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1893_, v_a_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; lean_object* v_env_1908_; uint8_t v___x_1909_; lean_object* v_env_1910_; lean_object* v___x_1911_; lean_object* v_toCold_1912_; lean_object* v_mctx_1913_; lean_object* v_lctx_1914_; lean_object* v_options_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1907_ = lean_st_ref_get(v___y_1905_);
v_env_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_env_1908_);
lean_dec(v___x_1907_);
v___x_1909_ = 0;
v_env_1910_ = l_Lean_Environment_setRecordingDeps(v_env_1908_, v___x_1909_);
v___x_1911_ = lean_st_ref_get(v___y_1903_);
v_toCold_1912_ = lean_ctor_get(v___y_1904_, 0);
v_mctx_1913_ = lean_ctor_get(v___x_1911_, 0);
lean_inc_ref(v_mctx_1913_);
lean_dec(v___x_1911_);
v_lctx_1914_ = lean_ctor_get(v___y_1902_, 2);
v_options_1915_ = lean_ctor_get(v_toCold_1912_, 2);
lean_inc_ref(v_options_1915_);
lean_inc_ref(v_lctx_1914_);
v___x_1916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1916_, 0, v_env_1910_);
lean_ctor_set(v___x_1916_, 1, v_mctx_1913_);
lean_ctor_set(v___x_1916_, 2, v_lctx_1914_);
lean_ctor_set(v___x_1916_, 3, v_options_1915_);
v___x_1917_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v_msgData_1901_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1926_; double v___x_1927_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = lean_float_of_nat(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1931_, lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_ref_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1985_; 
v_ref_1938_ = lean_ctor_get(v___y_1935_, 2);
v___x_1939_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1985_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1985_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v_traceState_1945_; lean_object* v_env_1946_; lean_object* v_nextMacroScope_1947_; lean_object* v_ngen_1948_; lean_object* v_auxDeclNGen_1949_; lean_object* v_cache_1950_; lean_object* v_recordedDeps_1951_; lean_object* v_messages_1952_; lean_object* v_infoState_1953_; lean_object* v_snapshotTasks_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1984_; 
v___x_1944_ = lean_st_ref_take(v___y_1936_);
v_traceState_1945_ = lean_ctor_get(v___x_1944_, 4);
v_env_1946_ = lean_ctor_get(v___x_1944_, 0);
v_nextMacroScope_1947_ = lean_ctor_get(v___x_1944_, 1);
v_ngen_1948_ = lean_ctor_get(v___x_1944_, 2);
v_auxDeclNGen_1949_ = lean_ctor_get(v___x_1944_, 3);
v_cache_1950_ = lean_ctor_get(v___x_1944_, 5);
v_recordedDeps_1951_ = lean_ctor_get(v___x_1944_, 6);
v_messages_1952_ = lean_ctor_get(v___x_1944_, 7);
v_infoState_1953_ = lean_ctor_get(v___x_1944_, 8);
v_snapshotTasks_1954_ = lean_ctor_get(v___x_1944_, 9);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1956_ = v___x_1944_;
v_isShared_1957_ = v_isSharedCheck_1984_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_snapshotTasks_1954_);
lean_inc(v_infoState_1953_);
lean_inc(v_messages_1952_);
lean_inc(v_recordedDeps_1951_);
lean_inc(v_cache_1950_);
lean_inc(v_traceState_1945_);
lean_inc(v_auxDeclNGen_1949_);
lean_inc(v_ngen_1948_);
lean_inc(v_nextMacroScope_1947_);
lean_inc(v_env_1946_);
lean_dec(v___x_1944_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1984_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
uint64_t v_tid_1958_; lean_object* v_traces_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1983_; 
v_tid_1958_ = lean_ctor_get_uint64(v_traceState_1945_, sizeof(void*)*1);
v_traces_1959_ = lean_ctor_get(v_traceState_1945_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_traceState_1945_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1961_ = v_traceState_1945_;
v_isShared_1962_ = v_isSharedCheck_1983_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_traces_1959_);
lean_dec(v_traceState_1945_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1983_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; double v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1966_ = 0;
v___x_1967_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1968_, 0, v_cls_1931_);
lean_ctor_set(v___x_1968_, 1, v___x_1964_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3, v___x_1965_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3 + 8, v___x_1965_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 16, v___x_1966_);
v___x_1969_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1970_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v_a_1940_);
lean_ctor_set(v___x_1970_, 2, v___x_1969_);
lean_inc(v_ref_1938_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_ref_1938_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_PersistentArray_push___redArg(v_traces_1959_, v___x_1971_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1972_);
v___x_1974_ = v___x_1961_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1972_);
lean_ctor_set_uint64(v_reuseFailAlloc_1982_, sizeof(void*)*1, v_tid_1958_);
v___x_1974_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v___x_1974_);
v___x_1976_ = v___x_1956_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_env_1946_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_nextMacroScope_1947_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_ngen_1948_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_auxDeclNGen_1949_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_cache_1950_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_recordedDeps_1951_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_messages_1952_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_infoState_1953_);
lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_snapshotTasks_1954_);
v___x_1976_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_st_ref_put(v___y_1936_, v___x_1976_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1963_);
v___x_1979_ = v___x_1942_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1963_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1986_, lean_object* v_msg_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1986_, v_msg_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1993_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_traceClass_1998_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_b_2002_);
return v___x_2009_;
}
else
{
lean_object* v_a_2010_; lean_object* v_snd_2011_; lean_object* v_fst_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2047_; 
v_a_2010_ = lean_array_uget(v_as_1999_, v_i_2001_);
v_snd_2011_ = lean_ctor_get(v_a_2010_, 1);
v_fst_2012_ = lean_ctor_get(v_a_2010_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_2010_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2014_ = v_a_2010_;
v_isShared_2015_ = v_isSharedCheck_2047_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_snd_2011_);
lean_inc(v_fst_2012_);
lean_dec(v_a_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2047_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_num_2016_; lean_object* v_den_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2046_; 
v_num_2016_ = lean_ctor_get(v_snd_2011_, 0);
v_den_2017_ = lean_ctor_get(v_snd_2011_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_snd_2011_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2019_ = v_snd_2011_;
v_isShared_2020_ = v_isSharedCheck_2046_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_den_2017_);
lean_inc(v_num_2016_);
lean_dec(v_snd_2011_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2046_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2021_ = lean_box(0);
v___x_2022_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2012_);
v___x_2023_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 7);
lean_ctor_set(v___x_2019_, 1, v___x_2023_);
lean_ctor_set(v___x_2019_, 0, v___x_2022_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___y_2027_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_unsigned_to_nat(1u);
v___x_2038_ = lean_nat_dec_eq(v_den_2017_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2039_ = l_Int_repr(v_num_2016_);
lean_dec(v_num_2016_);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2041_ = lean_string_append(v___x_2039_, v___x_2040_);
v___x_2042_ = l_Nat_reprFast(v_den_2017_);
v___x_2043_ = lean_string_append(v___x_2041_, v___x_2042_);
lean_dec_ref(v___x_2042_);
v___y_2027_ = v___x_2043_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2044_; 
lean_dec(v_den_2017_);
v___x_2044_ = l_Int_repr(v_num_2016_);
lean_dec(v_num_2016_);
v___y_2027_ = v___x_2044_;
goto v___jp_2026_;
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___y_2027_);
v___x_2029_ = l_Lean_MessageData_ofFormat(v___x_2028_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 7);
lean_ctor_set(v___x_2014_, 1, v___x_2029_);
lean_ctor_set(v___x_2014_, 0, v___x_2025_);
v___x_2031_ = v___x_2014_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; 
lean_inc(v_traceClass_1998_);
v___x_2032_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_1998_, v___x_2031_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2032_) == 0)
{
size_t v___x_2033_; size_t v___x_2034_; 
lean_dec_ref_known(v___x_2032_, 1);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2001_, v___x_2033_);
v_i_2001_ = v___x_2034_;
v_b_2002_ = v___x_2021_;
goto _start;
}
else
{
lean_dec(v_traceClass_1998_);
return v___x_2032_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2048_, lean_object* v_as_2049_, lean_object* v_sz_2050_, lean_object* v_i_2051_, lean_object* v_b_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2050_);
lean_dec(v_sz_2050_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2048_, v_as_2049_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_as_2049_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2064_, lean_object* v_model_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_toCold_2074_; lean_object* v_options_2075_; uint8_t v_hasTrace_2076_; 
v_toCold_2074_ = lean_ctor_get(v_a_2068_, 0);
v_options_2075_ = lean_ctor_get(v_toCold_2074_, 2);
v_hasTrace_2076_ = lean_ctor_get_uint8(v_options_2075_, sizeof(void*)*1);
if (v_hasTrace_2076_ == 0)
{
lean_dec(v_traceClass_2064_);
goto v___jp_2071_;
}
else
{
lean_object* v_inheritedTraceOptions_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_inheritedTraceOptions_2077_ = lean_ctor_get(v_toCold_2074_, 11);
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2064_);
v___x_2079_ = l_Lean_Name_append(v___x_2078_, v_traceClass_2064_);
v___x_2080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2077_, v_options_2075_, v___x_2079_);
lean_dec(v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v_traceClass_2064_);
goto v___jp_2071_;
}
else
{
lean_object* v___x_2081_; size_t v_sz_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v_sz_2082_ = lean_array_size(v_model_2065_);
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2064_, v_model_2065_, v_sz_2082_, v___x_2083_, v___x_2081_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2092_);
v___x_2086_ = v___x_2084_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v___x_2084_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2081_);
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2081_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
return v___x_2084_;
}
}
}
v___jp_2071_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2093_, lean_object* v_model_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2093_, v_model_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec_ref(v_model_2094_);
return v_res_2100_;
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
