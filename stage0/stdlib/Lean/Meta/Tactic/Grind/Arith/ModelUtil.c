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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object* v_goal_82_, lean_object* v_e_83_, lean_object* v_a_84_, lean_object* v_v_85_, lean_object* v_as_x27_86_, lean_object* v_b_87_){
_start:
{
if (lean_obj_tag(v_as_x27_86_) == 0)
{
lean_dec(v_v_85_);
lean_inc_ref(v_b_87_);
return v_b_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___y_93_; uint8_t v___y_94_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_head_88_ = lean_ctor_get(v_as_x27_86_, 0);
v_tail_89_ = lean_ctor_get(v_as_x27_86_, 1);
v___x_90_ = lean_box(0);
v___x_91_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_88_);
v___x_99_ = l_Lean_Expr_cleanupAnnotations(v_head_88_);
v___x_100_ = l_Lean_Expr_isApp(v___x_99_);
if (v___x_100_ == 0)
{
lean_dec_ref(v___x_99_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v_arg_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_arg_102_ = lean_ctor_get(v___x_99_, 1);
lean_inc_ref(v_arg_102_);
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_99_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v_arg_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_106_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_arg_106_);
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_111_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_112_ = l_Lean_Expr_isConstOf(v___x_110_, v___x_111_);
lean_dec_ref(v___x_110_);
if (v___x_112_ == 0)
{
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_head_88_);
if (lean_obj_tag(v___x_114_) == 1)
{
lean_object* v_val_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_val_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_val_115_);
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_117_ = l_Lean_Expr_isConstOf(v_val_115_, v___x_116_);
lean_dec(v_val_115_);
if (v___x_117_ == 0)
{
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_arg_106_);
lean_dec_ref(v_arg_106_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_121_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_arg_102_);
lean_dec_ref(v_arg_102_);
if (lean_obj_tag(v___x_121_) == 1)
{
lean_object* v_val_122_; uint8_t v___y_124_; uint8_t v___y_129_; uint8_t v___x_131_; 
v_val_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v___x_121_, 1);
v___x_131_ = lean_expr_eqv(v_val_120_, v_e_83_);
if (v___x_131_ == 0)
{
v___y_129_ = v___x_131_;
goto v___jp_128_;
}
else
{
uint8_t v___x_132_; 
lean_inc(v_v_85_);
v___x_132_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_84_, v_v_85_, v_val_122_);
if (v___x_132_ == 0)
{
v___y_129_ = v___x_117_;
goto v___jp_128_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
v___y_124_ = v___x_133_;
goto v___jp_123_;
}
}
v___jp_123_:
{
uint8_t v___x_125_; 
v___x_125_ = lean_expr_eqv(v_val_122_, v_e_83_);
lean_dec(v_val_122_);
if (v___x_125_ == 0)
{
lean_dec(v_val_120_);
v___y_93_ = v___y_124_;
v___y_94_ = v___x_125_;
goto v___jp_92_;
}
else
{
uint8_t v___x_126_; 
lean_inc(v_v_85_);
v___x_126_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_84_, v_v_85_, v_val_120_);
lean_dec(v_val_120_);
if (v___x_126_ == 0)
{
v___y_93_ = v___y_124_;
v___y_94_ = v___x_117_;
goto v___jp_92_;
}
else
{
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
}
}
v___jp_128_:
{
if (v___y_129_ == 0)
{
v___y_124_ = v___y_129_;
goto v___jp_123_;
}
else
{
lean_object* v___x_130_; 
lean_dec(v_val_122_);
lean_dec(v_val_120_);
lean_dec(v_v_85_);
v___x_130_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6));
return v___x_130_;
}
}
}
else
{
lean_dec(v___x_121_);
lean_dec(v_val_120_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
}
else
{
lean_dec(v___x_119_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
}
}
else
{
lean_dec(v___x_114_);
lean_dec_ref(v_arg_106_);
lean_dec_ref(v_arg_102_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
}
}
}
}
v___jp_92_:
{
if (v___y_94_ == 0)
{
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_91_;
goto _start;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_dec(v_v_85_);
v___x_96_ = lean_box(v___y_93_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_90_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_137_, lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_v_140_, lean_object* v_as_x27_141_, lean_object* v_b_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_137_, v_e_138_, v_a_139_, v_v_140_, v_as_x27_141_, v_b_142_);
lean_dec_ref(v_b_142_);
lean_dec(v_as_x27_141_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_e_138_);
lean_dec_ref(v_goal_137_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_144_, lean_object* v_vals_145_, lean_object* v_i_146_, lean_object* v_k_147_){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_array_get_size(v_keys_144_);
v___x_149_ = lean_nat_dec_lt(v_i_146_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; 
lean_dec(v_i_146_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v_k_x27_151_; size_t v___x_152_; size_t v___x_153_; uint8_t v___x_154_; 
v_k_x27_151_ = lean_array_fget_borrowed(v_keys_144_, v_i_146_);
v___x_152_ = lean_ptr_addr(v_k_147_);
v___x_153_ = lean_ptr_addr(v_k_x27_151_);
v___x_154_ = lean_usize_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_i_146_, v___x_155_);
lean_dec(v_i_146_);
v_i_146_ = v___x_156_;
goto _start;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_array_fget_borrowed(v_vals_145_, v_i_146_);
lean_dec(v_i_146_);
lean_inc(v___x_158_);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_i_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_160_, v_vals_161_, v_i_162_, v_k_163_);
lean_dec_ref(v_k_163_);
lean_dec_ref(v_vals_161_);
lean_dec_ref(v_keys_160_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_165_, size_t v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v_es_168_; lean_object* v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v_j_172_; lean_object* v___x_173_; 
v_es_168_ = lean_ctor_get(v_x_165_, 0);
v___x_169_ = lean_box(2);
v___x_170_ = ((size_t)31ULL);
v___x_171_ = lean_usize_land(v_x_166_, v___x_170_);
v_j_172_ = lean_usize_to_nat(v___x_171_);
v___x_173_ = lean_array_get_borrowed(v___x_169_, v_es_168_, v_j_172_);
lean_dec(v_j_172_);
switch(lean_obj_tag(v___x_173_))
{
case 0:
{
lean_object* v_key_174_; lean_object* v_val_175_; size_t v___x_176_; size_t v___x_177_; uint8_t v___x_178_; 
v_key_174_ = lean_ctor_get(v___x_173_, 0);
v_val_175_ = lean_ctor_get(v___x_173_, 1);
v___x_176_ = lean_ptr_addr(v_x_167_);
v___x_177_ = lean_ptr_addr(v_key_174_);
v___x_178_ = lean_usize_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
lean_inc(v_val_175_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_val_175_);
return v___x_180_;
}
}
case 1:
{
lean_object* v_node_181_; size_t v___x_182_; size_t v___x_183_; 
v_node_181_ = lean_ctor_get(v___x_173_, 0);
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_usize_shift_right(v_x_166_, v___x_182_);
v_x_165_ = v_node_181_;
v_x_166_ = v___x_183_;
goto _start;
}
default: 
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
}
}
else
{
lean_object* v_ks_186_; lean_object* v_vs_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_ks_186_ = lean_ctor_get(v_x_165_, 0);
v_vs_187_ = lean_ctor_get(v_x_165_, 1);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_186_, v_vs_187_, v___x_188_, v_x_167_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_1738__boxed_193_; lean_object* v_res_194_; 
v_x_1738__boxed_193_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_194_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_190_, v_x_1738__boxed_193_, v_x_192_);
lean_dec_ref(v_x_192_);
lean_dec_ref(v_x_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; uint64_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; 
v___x_197_ = lean_ptr_addr(v_x_196_);
v___x_198_ = ((size_t)3ULL);
v___x_199_ = lean_usize_shift_right(v___x_197_, v___x_198_);
v___x_200_ = lean_usize_to_uint64(v___x_199_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_195_, v___x_201_, v_x_196_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_203_, v_x_204_);
lean_dec_ref(v_x_204_);
lean_dec_ref(v_x_203_);
return v_res_205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_206_, lean_object* v_a_207_, lean_object* v_e_208_, lean_object* v_v_209_){
_start:
{
lean_object* v_toGoalState_210_; lean_object* v_parents_211_; lean_object* v___x_212_; 
v_toGoalState_210_ = lean_ctor_get(v_goal_206_, 0);
v_parents_211_ = lean_ctor_get(v_toGoalState_210_, 3);
v___x_212_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_211_, v_e_208_);
if (lean_obj_tag(v___x_212_) == 1)
{
lean_object* v_val_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_fst_217_; 
v_val_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_213_);
lean_dec(v_val_213_);
v___x_215_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_216_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_206_, v_e_208_, v_a_207_, v_v_209_, v___x_214_, v___x_215_);
lean_dec(v___x_214_);
v_fst_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_fst_217_);
lean_dec_ref(v___x_216_);
if (lean_obj_tag(v_fst_217_) == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 1;
return v___x_218_;
}
else
{
lean_object* v_val_219_; uint8_t v___x_220_; 
v_val_219_ = lean_ctor_get(v_fst_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v_fst_217_, 1);
v___x_220_ = lean_unbox(v_val_219_);
lean_dec(v_val_219_);
return v___x_220_;
}
}
else
{
uint8_t v___x_221_; 
lean_dec(v___x_212_);
lean_dec(v_v_209_);
v___x_221_ = 1;
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_222_, lean_object* v_a_223_, lean_object* v_e_224_, lean_object* v_v_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_222_, v_a_223_, v_e_224_, v_v_225_);
lean_dec_ref(v_e_224_);
lean_dec_ref(v_a_223_);
lean_dec_ref(v_goal_222_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_229_, v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_232_, v_x_233_, v_x_234_);
lean_dec_ref(v_x_234_);
lean_dec_ref(v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_236_, lean_object* v_e_237_, lean_object* v_a_238_, lean_object* v_v_239_, lean_object* v_as_240_, lean_object* v_as_x27_241_, lean_object* v_b_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_236_, v_e_237_, v_a_238_, v_v_239_, v_as_x27_241_, v_b_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_245_, lean_object* v_e_246_, lean_object* v_a_247_, lean_object* v_v_248_, lean_object* v_as_249_, lean_object* v_as_x27_250_, lean_object* v_b_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_245_, v_e_246_, v_a_247_, v_v_248_, v_as_249_, v_as_x27_250_, v_b_251_, v_a_252_);
lean_dec_ref(v_b_251_);
lean_dec(v_as_x27_250_);
lean_dec(v_as_249_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_e_246_);
lean_dec_ref(v_goal_245_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_254_, lean_object* v_x_255_, size_t v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_255_, v_x_256_, v_x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
size_t v_x_1843__boxed_263_; lean_object* v_res_264_; 
v_x_1843__boxed_263_ = lean_unbox_usize(v_x_261_);
lean_dec(v_x_261_);
v_res_264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_259_, v_x_260_, v_x_1843__boxed_263_, v_x_262_);
lean_dec_ref(v_x_262_);
lean_dec_ref(v_x_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_265_, lean_object* v_keys_266_, lean_object* v_vals_267_, lean_object* v_heq_268_, lean_object* v_i_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_266_, v_vals_267_, v_i_269_, v_k_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_272_, lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_heq_275_, lean_object* v_i_276_, lean_object* v_k_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_272_, v_keys_273_, v_vals_274_, v_heq_275_, v_i_276_, v_k_277_);
lean_dec_ref(v_k_277_);
lean_dec_ref(v_vals_274_);
lean_dec_ref(v_keys_273_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
else
{
lean_object* v_key_282_; lean_object* v_tail_283_; uint8_t v___x_284_; 
v_key_282_ = lean_ctor_get(v_x_280_, 0);
v_tail_283_ = lean_ctor_get(v_x_280_, 2);
v___x_284_ = lean_int_dec_eq(v_key_282_, v_a_279_);
if (v___x_284_ == 0)
{
v_x_280_ = v_tail_283_;
goto _start;
}
else
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_286_, v_x_287_);
lean_dec(v_x_287_);
lean_dec(v_a_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_290_; lean_object* v_intZero_291_; 
v_natZero_290_ = lean_unsigned_to_nat(0u);
v_intZero_291_ = lean_nat_to_int(v_natZero_290_);
return v_intZero_291_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_buckets_294_; lean_object* v___x_295_; uint64_t v___y_297_; lean_object* v_intZero_311_; uint8_t v_isNeg_312_; 
v_buckets_294_ = lean_ctor_get(v_m_292_, 1);
v___x_295_ = lean_array_get_size(v_buckets_294_);
v_intZero_311_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_312_ = lean_int_dec_lt(v_a_293_, v_intZero_311_);
if (v_isNeg_312_ == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint64_t v___x_316_; 
v_a_313_ = lean_nat_abs(v_a_293_);
v___x_314_ = lean_unsigned_to_nat(2u);
v___x_315_ = lean_nat_mul(v___x_314_, v_a_313_);
lean_dec(v_a_313_);
v___x_316_ = lean_uint64_of_nat(v___x_315_);
lean_dec(v___x_315_);
v___y_297_ = v___x_316_;
goto v___jp_296_;
}
else
{
lean_object* v_abs_317_; lean_object* v_one_318_; lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint64_t v___x_323_; 
v_abs_317_ = lean_nat_abs(v_a_293_);
v_one_318_ = lean_unsigned_to_nat(1u);
v_a_319_ = lean_nat_sub(v_abs_317_, v_one_318_);
lean_dec(v_abs_317_);
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_nat_mul(v___x_320_, v_a_319_);
lean_dec(v_a_319_);
v___x_322_ = lean_nat_add(v___x_321_, v_one_318_);
lean_dec(v___x_321_);
v___x_323_ = lean_uint64_of_nat(v___x_322_);
lean_dec(v___x_322_);
v___y_297_ = v___x_323_;
goto v___jp_296_;
}
v___jp_296_:
{
uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v_fold_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_298_ = 32ULL;
v___x_299_ = lean_uint64_shift_right(v___y_297_, v___x_298_);
v_fold_300_ = lean_uint64_xor(v___y_297_, v___x_299_);
v___x_301_ = 16ULL;
v___x_302_ = lean_uint64_shift_right(v_fold_300_, v___x_301_);
v___x_303_ = lean_uint64_xor(v_fold_300_, v___x_302_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = lean_usize_of_nat(v___x_295_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v___x_305_, v___x_306_);
v___x_308_ = lean_usize_land(v___x_304_, v___x_307_);
v___x_309_ = lean_array_uget_borrowed(v_buckets_294_, v___x_308_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_293_, v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_m_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_to_int(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_330_, lean_object* v_a_331_, lean_object* v_e_332_, lean_object* v_alreadyUsed_333_, lean_object* v_next_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_333_, v_next_334_);
if (v___x_335_ == 0)
{
uint8_t v___x_336_; 
lean_inc(v_next_334_);
v___x_336_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_330_, v_a_331_, v_e_332_, v_next_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_338_ = lean_int_add(v_next_334_, v___x_337_);
lean_dec(v_next_334_);
v_next_334_ = v___x_338_;
goto _start;
}
else
{
return v_next_334_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_341_ = lean_int_add(v_next_334_, v___x_340_);
lean_dec(v_next_334_);
v_next_334_ = v___x_341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_343_, lean_object* v_a_344_, lean_object* v_e_345_, lean_object* v_alreadyUsed_346_, lean_object* v_next_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_343_, v_a_344_, v_e_345_, v_alreadyUsed_346_, v_next_347_);
lean_dec_ref(v_alreadyUsed_346_);
lean_dec_ref(v_e_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_goal_343_);
return v_res_348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_349_, lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_350_, v_a_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_a_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_353_, v_m_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_m_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_358_, lean_object* v_a_359_, lean_object* v_x_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_359_, v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_362_, lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_362_, v_a_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec(v_a_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_367_, lean_object* v_a_368_, lean_object* v_e_369_, lean_object* v_next_370_, lean_object* v_alreadyUsed_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_367_, v_a_368_, v_e_369_, v_alreadyUsed_371_, v_next_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_373_, lean_object* v_a_374_, lean_object* v_e_375_, lean_object* v_next_376_, lean_object* v_alreadyUsed_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_373_, v_a_374_, v_e_375_, v_next_376_, v_alreadyUsed_377_);
lean_dec_ref(v_alreadyUsed_377_);
lean_dec_ref(v_e_375_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_goal_373_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_464_){
_start:
{
uint8_t v___y_471_; uint8_t v___x_504_; 
lean_inc_ref(v_e_464_);
v___x_504_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_464_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_inc_ref(v_e_464_);
v___x_505_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_464_);
v___y_471_ = v___x_505_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___x_504_;
goto v___jp_470_;
}
v___jp_465_:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_467_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4));
v___x_469_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_468_);
lean_dec_ref(v_e_464_);
return v___x_469_;
}
else
{
lean_dec_ref(v_e_464_);
return v___x_467_;
}
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7));
v___x_473_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10));
v___x_475_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13));
v___x_477_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16));
v___x_479_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19));
v___x_481_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22));
v___x_483_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25));
v___x_485_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28));
v___x_487_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31));
v___x_489_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34));
v___x_491_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37));
v___x_493_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_492_);
if (v___x_493_ == 0)
{
uint8_t v___x_494_; 
v___x_494_ = l_Lean_Expr_isIte(v_e_464_);
if (v___x_494_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Expr_isDIte(v_e_464_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_497_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_499_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__49));
v___x_501_ = l_Lean_Expr_isAppOf(v_e_464_, v___x_500_);
if (v___x_501_ == 0)
{
if (lean_obj_tag(v_e_464_) == 9)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v_e_464_, 0);
if (lean_obj_tag(v_a_502_) == 0)
{
uint8_t v___x_503_; 
lean_dec_ref_known(v_e_464_, 1);
v___x_503_ = 1;
return v___x_503_;
}
else
{
goto v___jp_465_;
}
}
else
{
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_501_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_499_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_497_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_494_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_493_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_491_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_489_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_485_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_483_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_481_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_479_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_475_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___x_473_;
}
}
else
{
lean_dec_ref(v_e_464_);
return v___y_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_509_;
}
else
{
lean_object* v_key_511_; lean_object* v_value_512_; lean_object* v_tail_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_536_; 
v_key_511_ = lean_ctor_get(v_x_510_, 0);
v_value_512_ = lean_ctor_get(v_x_510_, 1);
v_tail_513_ = lean_ctor_get(v_x_510_, 2);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_510_);
if (v_isSharedCheck_536_ == 0)
{
v___x_515_ = v_x_510_;
v_isShared_516_ = v_isSharedCheck_536_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_tail_513_);
lean_inc(v_value_512_);
lean_inc(v_key_511_);
lean_dec(v_x_510_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_536_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v_fold_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_517_ = lean_array_get_size(v_x_509_);
v___x_518_ = l_Lean_Expr_hash(v_key_511_);
v___x_519_ = 32ULL;
v___x_520_ = lean_uint64_shift_right(v___x_518_, v___x_519_);
v_fold_521_ = lean_uint64_xor(v___x_518_, v___x_520_);
v___x_522_ = 16ULL;
v___x_523_ = lean_uint64_shift_right(v_fold_521_, v___x_522_);
v___x_524_ = lean_uint64_xor(v_fold_521_, v___x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = lean_usize_of_nat(v___x_517_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_usize_land(v___x_525_, v___x_528_);
v___x_530_ = lean_array_uget_borrowed(v_x_509_, v___x_529_);
lean_inc(v___x_530_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 2, v___x_530_);
v___x_532_ = v___x_515_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_key_511_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_value_512_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v___x_530_);
v___x_532_ = v_reuseFailAlloc_535_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; 
v___x_533_ = lean_array_uset(v_x_509_, v___x_529_, v___x_532_);
v_x_509_ = v___x_533_;
v_x_510_ = v_tail_513_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_537_, lean_object* v_source_538_, lean_object* v_target_539_){
_start:
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_array_get_size(v_source_538_);
v___x_541_ = lean_nat_dec_lt(v_i_537_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec_ref(v_source_538_);
lean_dec(v_i_537_);
return v_target_539_;
}
else
{
lean_object* v_es_542_; lean_object* v___x_543_; lean_object* v_source_544_; lean_object* v_target_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_es_542_ = lean_array_fget(v_source_538_, v_i_537_);
v___x_543_ = lean_box(0);
v_source_544_ = lean_array_fset(v_source_538_, v_i_537_, v___x_543_);
v_target_545_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_539_, v_es_542_);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_i_537_, v___x_546_);
lean_dec(v_i_537_);
v_i_537_ = v___x_547_;
v_source_538_ = v_source_544_;
v_target_539_ = v_target_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_549_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_nbuckets_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_550_ = lean_array_get_size(v_data_549_);
v___x_551_ = lean_unsigned_to_nat(2u);
v_nbuckets_552_ = lean_nat_mul(v___x_550_, v___x_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_box(0);
v___x_555_ = lean_mk_array(v_nbuckets_552_, v___x_554_);
v___x_556_ = lean_array_propagate_mark(v_data_549_, v___x_555_);
v___x_557_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_553_, v_data_549_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_558_, lean_object* v_b_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_dec(v_b_559_);
lean_dec_ref(v_a_558_);
return v_x_560_;
}
else
{
lean_object* v_key_561_; lean_object* v_value_562_; lean_object* v_tail_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_575_; 
v_key_561_ = lean_ctor_get(v_x_560_, 0);
v_value_562_ = lean_ctor_get(v_x_560_, 1);
v_tail_563_ = lean_ctor_get(v_x_560_, 2);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_560_);
if (v_isSharedCheck_575_ == 0)
{
v___x_565_ = v_x_560_;
v_isShared_566_ = v_isSharedCheck_575_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_tail_563_);
lean_inc(v_value_562_);
lean_inc(v_key_561_);
lean_dec(v_x_560_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_575_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = lean_expr_eqv(v_key_561_, v_a_558_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_558_, v_b_559_, v_tail_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 2, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_key_561_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_value_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v_value_562_);
lean_dec(v_key_561_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_b_559_);
lean_ctor_set(v___x_565_, 0, v_a_558_);
v___x_573_ = v___x_565_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_558_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_b_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_tail_563_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
uint8_t v___x_578_; 
v___x_578_ = 0;
return v___x_578_;
}
else
{
lean_object* v_key_579_; lean_object* v_tail_580_; uint8_t v___x_581_; 
v_key_579_ = lean_ctor_get(v_x_577_, 0);
v_tail_580_ = lean_ctor_get(v_x_577_, 2);
v___x_581_ = lean_expr_eqv(v_key_579_, v_a_576_);
if (v___x_581_ == 0)
{
v_x_577_ = v_tail_580_;
goto _start;
}
else
{
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
uint8_t v_res_585_; lean_object* v_r_586_; 
v_res_585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_583_, v_x_584_);
lean_dec(v_x_584_);
lean_dec_ref(v_a_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_size_590_; lean_object* v_buckets_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_634_; 
v_size_590_ = lean_ctor_get(v_m_587_, 0);
v_buckets_591_ = lean_ctor_get(v_m_587_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_m_587_);
if (v_isSharedCheck_634_ == 0)
{
v___x_593_ = v_m_587_;
v_isShared_594_ = v_isSharedCheck_634_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_buckets_591_);
lean_inc(v_size_590_);
lean_dec(v_m_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_634_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v_fold_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; lean_object* v_bkt_608_; uint8_t v___x_609_; 
v___x_595_ = lean_array_get_size(v_buckets_591_);
v___x_596_ = l_Lean_Expr_hash(v_a_588_);
v___x_597_ = 32ULL;
v___x_598_ = lean_uint64_shift_right(v___x_596_, v___x_597_);
v_fold_599_ = lean_uint64_xor(v___x_596_, v___x_598_);
v___x_600_ = 16ULL;
v___x_601_ = lean_uint64_shift_right(v_fold_599_, v___x_600_);
v___x_602_ = lean_uint64_xor(v_fold_599_, v___x_601_);
v___x_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = lean_usize_of_nat(v___x_595_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_sub(v___x_604_, v___x_605_);
v___x_607_ = lean_usize_land(v___x_603_, v___x_606_);
v_bkt_608_ = lean_array_uget_borrowed(v_buckets_591_, v___x_607_);
v___x_609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_588_, v_bkt_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v_size_x27_611_; lean_object* v___x_612_; lean_object* v_buckets_x27_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v_size_x27_611_ = lean_nat_add(v_size_590_, v___x_610_);
lean_dec(v_size_590_);
lean_inc(v_bkt_608_);
v___x_612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_612_, 0, v_a_588_);
lean_ctor_set(v___x_612_, 1, v_b_589_);
lean_ctor_set(v___x_612_, 2, v_bkt_608_);
v_buckets_x27_613_ = lean_array_uset(v_buckets_591_, v___x_607_, v___x_612_);
v___x_614_ = lean_unsigned_to_nat(4u);
v___x_615_ = lean_nat_mul(v_size_x27_611_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(3u);
v___x_617_ = lean_nat_div(v___x_615_, v___x_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_array_get_size(v_buckets_x27_613_);
v___x_619_ = lean_nat_dec_le(v___x_617_, v___x_618_);
lean_dec(v___x_617_);
if (v___x_619_ == 0)
{
lean_object* v_val_620_; lean_object* v___x_622_; 
v_val_620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_613_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_val_620_);
lean_ctor_set(v___x_593_, 0, v_size_x27_611_);
v___x_622_ = v___x_593_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_size_x27_611_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_val_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v___x_625_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_buckets_x27_613_);
lean_ctor_set(v___x_593_, 0, v_size_x27_611_);
v___x_625_ = v___x_593_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_size_x27_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_buckets_x27_613_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v_buckets_x27_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_inc(v_bkt_608_);
v___x_627_ = lean_box(0);
v_buckets_x27_628_ = lean_array_uset(v_buckets_591_, v___x_607_, v___x_627_);
v___x_629_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_588_, v_b_589_, v_bkt_608_);
v___x_630_ = lean_array_uset(v_buckets_x27_628_, v___x_607_, v___x_629_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_630_);
v___x_632_ = v___x_593_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_size_590_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_635_, lean_object* v_as_x27_636_, lean_object* v_b_637_){
_start:
{
if (lean_obj_tag(v_as_x27_636_) == 0)
{
lean_dec_ref(v_v_635_);
return v_b_637_;
}
else
{
lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_640_; 
v_head_638_ = lean_ctor_get(v_as_x27_636_, 0);
v_tail_639_ = lean_ctor_get(v_as_x27_636_, 1);
lean_inc_ref(v_v_635_);
lean_inc(v_head_638_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_637_, v_head_638_, v_v_635_);
v_as_x27_636_ = v_tail_639_;
v_b_637_ = v___x_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_642_, lean_object* v_as_x27_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_642_, v_as_x27_643_, v_b_644_);
lean_dec(v_as_x27_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_646_, lean_object* v_e_647_, lean_object* v_v_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = 0;
v___x_651_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_646_, v_e_647_, v___x_650_);
v___x_652_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_648_, v___x_651_, v_a_649_);
lean_dec(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_653_, lean_object* v_e_654_, lean_object* v_v_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_653_, v_e_654_, v_v_655_, v_a_656_);
lean_dec_ref(v_goal_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_658_, lean_object* v_m_659_, lean_object* v_a_660_, lean_object* v_b_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_659_, v_a_660_, v_b_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_663_, lean_object* v_as_664_, lean_object* v_as_x27_665_, lean_object* v_b_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_663_, v_as_x27_665_, v_b_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_669_, lean_object* v_as_670_, lean_object* v_as_x27_671_, lean_object* v_b_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_669_, v_as_670_, v_as_x27_671_, v_b_672_, v_a_673_);
lean_dec(v_as_x27_671_);
lean_dec(v_as_670_);
return v_res_674_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_675_, lean_object* v_a_676_, lean_object* v_x_677_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_676_, v_x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_679_, lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_679_, v_a_680_, v_x_681_);
lean_dec(v_x_681_);
lean_dec_ref(v_a_680_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_684_, lean_object* v_data_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_687_, lean_object* v_a_688_, lean_object* v_b_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_688_, v_b_689_, v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_692_, lean_object* v_i_693_, lean_object* v_source_694_, lean_object* v_target_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_693_, v_source_694_, v_target_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_698_, v_x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
return v_x_701_;
}
else
{
lean_object* v_key_703_; lean_object* v_value_704_; lean_object* v_tail_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_742_; 
v_key_703_ = lean_ctor_get(v_x_702_, 0);
v_value_704_ = lean_ctor_get(v_x_702_, 1);
v_tail_705_ = lean_ctor_get(v_x_702_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_702_);
if (v_isSharedCheck_742_ == 0)
{
v___x_707_ = v_x_702_;
v_isShared_708_ = v_isSharedCheck_742_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_tail_705_);
lean_inc(v_value_704_);
lean_inc(v_key_703_);
lean_dec(v_x_702_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_742_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; uint64_t v___y_711_; lean_object* v_intZero_729_; uint8_t v_isNeg_730_; 
v___x_709_ = lean_array_get_size(v_x_701_);
v_intZero_729_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_730_ = lean_int_dec_lt(v_key_703_, v_intZero_729_);
if (v_isNeg_730_ == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint64_t v___x_734_; 
v_a_731_ = lean_nat_abs(v_key_703_);
v___x_732_ = lean_unsigned_to_nat(2u);
v___x_733_ = lean_nat_mul(v___x_732_, v_a_731_);
lean_dec(v_a_731_);
v___x_734_ = lean_uint64_of_nat(v___x_733_);
lean_dec(v___x_733_);
v___y_711_ = v___x_734_;
goto v___jp_710_;
}
else
{
lean_object* v_abs_735_; lean_object* v_one_736_; lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint64_t v___x_741_; 
v_abs_735_ = lean_nat_abs(v_key_703_);
v_one_736_ = lean_unsigned_to_nat(1u);
v_a_737_ = lean_nat_sub(v_abs_735_, v_one_736_);
lean_dec(v_abs_735_);
v___x_738_ = lean_unsigned_to_nat(2u);
v___x_739_ = lean_nat_mul(v___x_738_, v_a_737_);
lean_dec(v_a_737_);
v___x_740_ = lean_nat_add(v___x_739_, v_one_736_);
lean_dec(v___x_739_);
v___x_741_ = lean_uint64_of_nat(v___x_740_);
lean_dec(v___x_740_);
v___y_711_ = v___x_741_;
goto v___jp_710_;
}
v___jp_710_:
{
uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___y_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___y_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_709_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v___x_723_ = lean_array_uget_borrowed(v_x_701_, v___x_722_);
lean_inc(v___x_723_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 2, v___x_723_);
v___x_725_ = v___x_707_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_key_703_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_value_704_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_723_);
v___x_725_ = v_reuseFailAlloc_728_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_array_uset(v_x_701_, v___x_722_, v___x_725_);
v_x_701_ = v___x_726_;
v_x_702_ = v_tail_705_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_743_, lean_object* v_source_744_, lean_object* v_target_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_source_744_);
v___x_747_ = lean_nat_dec_lt(v_i_743_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_source_744_);
lean_dec(v_i_743_);
return v_target_745_;
}
else
{
lean_object* v_es_748_; lean_object* v___x_749_; lean_object* v_source_750_; lean_object* v_target_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_es_748_ = lean_array_fget(v_source_744_, v_i_743_);
v___x_749_ = lean_box(0);
v_source_750_ = lean_array_fset(v_source_744_, v_i_743_, v___x_749_);
v_target_751_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_745_, v_es_748_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_i_743_, v___x_752_);
lean_dec(v_i_743_);
v_i_743_ = v___x_753_;
v_source_744_ = v_source_750_;
v_target_745_ = v_target_751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_nbuckets_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_756_ = lean_array_get_size(v_data_755_);
v___x_757_ = lean_unsigned_to_nat(2u);
v_nbuckets_758_ = lean_nat_mul(v___x_756_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_box(0);
v___x_761_ = lean_mk_array(v_nbuckets_758_, v___x_760_);
v___x_762_ = lean_array_propagate_mark(v_data_755_, v___x_761_);
v___x_763_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_759_, v_data_755_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_size_767_; lean_object* v_buckets_768_; lean_object* v___x_769_; uint64_t v___y_771_; lean_object* v_intZero_808_; uint8_t v_isNeg_809_; 
v_size_767_ = lean_ctor_get(v_m_764_, 0);
v_buckets_768_ = lean_ctor_get(v_m_764_, 1);
v___x_769_ = lean_array_get_size(v_buckets_768_);
v_intZero_808_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_809_ = lean_int_dec_lt(v_a_765_, v_intZero_808_);
if (v_isNeg_809_ == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint64_t v___x_813_; 
v_a_810_ = lean_nat_abs(v_a_765_);
v___x_811_ = lean_unsigned_to_nat(2u);
v___x_812_ = lean_nat_mul(v___x_811_, v_a_810_);
lean_dec(v_a_810_);
v___x_813_ = lean_uint64_of_nat(v___x_812_);
lean_dec(v___x_812_);
v___y_771_ = v___x_813_;
goto v___jp_770_;
}
else
{
lean_object* v_abs_814_; lean_object* v_one_815_; lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint64_t v___x_820_; 
v_abs_814_ = lean_nat_abs(v_a_765_);
v_one_815_ = lean_unsigned_to_nat(1u);
v_a_816_ = lean_nat_sub(v_abs_814_, v_one_815_);
lean_dec(v_abs_814_);
v___x_817_ = lean_unsigned_to_nat(2u);
v___x_818_ = lean_nat_mul(v___x_817_, v_a_816_);
lean_dec(v_a_816_);
v___x_819_ = lean_nat_add(v___x_818_, v_one_815_);
lean_dec(v___x_818_);
v___x_820_ = lean_uint64_of_nat(v___x_819_);
lean_dec(v___x_819_);
v___y_771_ = v___x_820_;
goto v___jp_770_;
}
v___jp_770_:
{
uint64_t v___x_772_; uint64_t v___x_773_; uint64_t v_fold_774_; uint64_t v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; lean_object* v_bkt_783_; uint8_t v___x_784_; 
v___x_772_ = 32ULL;
v___x_773_ = lean_uint64_shift_right(v___y_771_, v___x_772_);
v_fold_774_ = lean_uint64_xor(v___y_771_, v___x_773_);
v___x_775_ = 16ULL;
v___x_776_ = lean_uint64_shift_right(v_fold_774_, v___x_775_);
v___x_777_ = lean_uint64_xor(v_fold_774_, v___x_776_);
v___x_778_ = lean_uint64_to_usize(v___x_777_);
v___x_779_ = lean_usize_of_nat(v___x_769_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_sub(v___x_779_, v___x_780_);
v___x_782_ = lean_usize_land(v___x_778_, v___x_781_);
v_bkt_783_ = lean_array_uget_borrowed(v_buckets_768_, v___x_782_);
v___x_784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_765_, v_bkt_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_805_; 
lean_inc_ref(v_buckets_768_);
lean_inc(v_size_767_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_m_764_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_806_ = lean_ctor_get(v_m_764_, 1);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_m_764_, 0);
lean_dec(v_unused_807_);
v___x_786_ = v_m_764_;
v_isShared_787_ = v_isSharedCheck_805_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_m_764_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_805_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v_size_x27_789_; lean_object* v___x_790_; lean_object* v_buckets_x27_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v_size_x27_789_ = lean_nat_add(v_size_767_, v___x_788_);
lean_dec(v_size_767_);
lean_inc(v_bkt_783_);
v___x_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_790_, 0, v_a_765_);
lean_ctor_set(v___x_790_, 1, v_b_766_);
lean_ctor_set(v___x_790_, 2, v_bkt_783_);
v_buckets_x27_791_ = lean_array_uset(v_buckets_768_, v___x_782_, v___x_790_);
v___x_792_ = lean_unsigned_to_nat(4u);
v___x_793_ = lean_nat_mul(v_size_x27_789_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(3u);
v___x_795_ = lean_nat_div(v___x_793_, v___x_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_array_get_size(v_buckets_x27_791_);
v___x_797_ = lean_nat_dec_le(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v_val_798_; lean_object* v___x_800_; 
v_val_798_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_791_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v_val_798_);
lean_ctor_set(v___x_786_, 0, v_size_x27_789_);
v___x_800_ = v___x_786_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_size_x27_789_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_val_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
lean_object* v___x_803_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v_buckets_x27_791_);
lean_ctor_set(v___x_786_, 0, v_size_x27_789_);
v___x_803_ = v___x_786_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_size_x27_789_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_buckets_x27_791_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_dec(v_b_766_);
lean_dec(v_a_765_);
return v_m_764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_821_, lean_object* v_isTarget_822_, lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec_ref(v_isTarget_822_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_b_826_);
return v___x_833_;
}
else
{
lean_object* v_snd_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_916_; 
v_snd_834_ = lean_ctor_get(v_b_826_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_b_826_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_b_826_, 0);
lean_dec(v_unused_917_);
v___x_836_ = v_b_826_;
v_isShared_837_ = v_isSharedCheck_916_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_snd_834_);
lean_dec(v_b_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_916_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
lean_inc(v_a_838_);
v___x_839_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_821_, v_a_838_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_snd_840_; lean_object* v_a_841_; lean_object* v_fst_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_906_; 
v_snd_840_ = lean_ctor_get(v_snd_834_, 1);
lean_inc(v_snd_840_);
v_a_841_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_839_, 1);
v_fst_842_ = lean_ctor_get(v_snd_834_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_snd_834_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_snd_834_, 1);
lean_dec(v_unused_907_);
v___x_844_ = v_snd_834_;
v_isShared_845_ = v_isSharedCheck_906_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_fst_842_);
lean_dec(v_snd_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_906_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_905_; 
v_fst_846_ = lean_ctor_get(v_snd_840_, 0);
v_snd_847_ = lean_ctor_get(v_snd_840_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_snd_840_);
if (v_isSharedCheck_905_ == 0)
{
v___x_849_ = v_snd_840_;
v_isShared_850_ = v_isSharedCheck_905_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_846_);
lean_dec(v_snd_840_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_905_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v_a_853_; uint8_t v___x_860_; 
v___x_851_ = lean_box(0);
v___x_860_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_841_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; 
lean_dec(v_a_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_snd_847_);
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_862_ = v___x_844_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_snd_847_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_862_);
lean_ctor_set(v___x_836_, 0, v_fst_842_);
v___x_864_ = v___x_836_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
v_a_853_ = v___x_864_;
goto v___jp_852_;
}
}
}
else
{
lean_object* v___x_867_; 
lean_inc_ref(v_isTarget_822_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v_a_841_);
v___x_867_ = lean_apply_6(v_isTarget_822_, v_a_841_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, lean_box(0));
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; uint8_t v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_unbox(v_a_868_);
lean_dec(v_a_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_a_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_snd_847_);
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_871_ = v___x_844_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_snd_847_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_871_);
lean_ctor_set(v___x_836_, 0, v_fst_842_);
v___x_873_ = v___x_836_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v_a_853_ = v___x_873_;
goto v___jp_852_;
}
}
}
else
{
lean_object* v_self_876_; lean_object* v___x_877_; 
v_self_876_ = lean_ctor_get(v_a_841_, 0);
lean_inc_ref(v_self_876_);
lean_dec(v_a_841_);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_847_, v_self_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_878_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_821_, v_snd_847_, v_self_876_, v_fst_846_, v_fst_842_);
lean_inc_n(v___x_878_, 2);
v___x_879_ = l_Rat_ofInt(v___x_878_);
v___x_880_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_821_, v_self_876_, v___x_879_, v_snd_847_);
v___x_881_ = lean_box(0);
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_846_, v___x_878_, v___x_881_);
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_884_ = lean_int_add(v___x_878_, v___x_883_);
lean_dec(v___x_878_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_880_);
lean_ctor_set(v___x_844_, 0, v___x_882_);
v___x_886_ = v___x_844_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_880_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_886_);
lean_ctor_set(v___x_836_, 0, v___x_884_);
v___x_888_ = v___x_836_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_a_853_ = v___x_888_;
goto v___jp_852_;
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec_ref_known(v___x_877_, 1);
lean_dec_ref(v_self_876_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_snd_847_);
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_892_ = v___x_844_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_847_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_892_);
lean_ctor_set(v___x_836_, 0, v_fst_842_);
v___x_894_ = v___x_836_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
v_a_853_ = v___x_894_;
goto v___jp_852_;
}
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_849_);
lean_dec(v_snd_847_);
lean_dec(v_fst_846_);
lean_del_object(v___x_844_);
lean_dec(v_fst_842_);
lean_dec(v_a_841_);
lean_del_object(v___x_836_);
lean_dec_ref(v_isTarget_822_);
v_a_897_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_867_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_867_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
v___jp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v_a_853_);
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_a_853_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
size_t v___x_856_; size_t v___x_857_; 
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_i_825_, v___x_856_);
v_i_825_ = v___x_857_;
v_b_826_ = v___x_855_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_836_);
lean_dec(v_snd_834_);
lean_dec_ref(v_isTarget_822_);
v_a_908_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_839_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_839_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_918_, lean_object* v_isTarget_919_, lean_object* v_as_920_, lean_object* v_sz_921_, lean_object* v_i_922_, lean_object* v_b_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_921_);
lean_dec(v_sz_921_);
v_i_boxed_930_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_918_, v_isTarget_919_, v_as_920_, v_sz_boxed_929_, v_i_boxed_930_, v_b_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v_as_920_);
lean_dec_ref(v_goal_918_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_932_, lean_object* v_isTarget_933_, lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = lean_usize_dec_lt(v_i_936_, v_sz_935_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v_isTarget_933_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_937_);
return v___x_944_;
}
else
{
lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1027_; 
v_snd_945_ = lean_ctor_get(v_b_937_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_b_937_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_b_937_, 0);
lean_dec(v_unused_1028_);
v___x_947_ = v_b_937_;
v_isShared_948_ = v_isSharedCheck_1027_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_dec(v_b_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1027_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_array_uget_borrowed(v_as_934_, v_i_936_);
lean_inc(v_a_949_);
v___x_950_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_932_, v_a_949_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_snd_951_; lean_object* v_a_952_; lean_object* v_fst_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1017_; 
v_snd_951_ = lean_ctor_get(v_snd_945_, 1);
lean_inc(v_snd_951_);
v_a_952_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_950_, 1);
v_fst_953_ = lean_ctor_get(v_snd_945_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_snd_945_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_snd_945_, 1);
lean_dec(v_unused_1018_);
v___x_955_ = v_snd_945_;
v_isShared_956_ = v_isSharedCheck_1017_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_fst_953_);
lean_dec(v_snd_945_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1017_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_fst_957_; lean_object* v_snd_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1016_; 
v_fst_957_ = lean_ctor_get(v_snd_951_, 0);
v_snd_958_ = lean_ctor_get(v_snd_951_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_snd_951_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_960_ = v_snd_951_;
v_isShared_961_ = v_isSharedCheck_1016_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_958_);
lean_inc(v_fst_957_);
lean_dec(v_snd_951_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1016_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v_a_964_; uint8_t v___x_971_; 
v___x_962_ = lean_box(0);
v___x_971_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_952_);
if (v___x_971_ == 0)
{
lean_object* v___x_973_; 
lean_dec(v_a_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_snd_958_);
lean_ctor_set(v___x_955_, 0, v_fst_957_);
v___x_973_ = v___x_955_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_snd_958_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_973_);
lean_ctor_set(v___x_947_, 0, v_fst_953_);
v___x_975_ = v___x_947_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fst_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v_a_964_ = v___x_975_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v___x_978_; 
lean_inc_ref(v_isTarget_933_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v_a_952_);
v___x_978_ = lean_apply_6(v_isTarget_933_, v_a_952_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, lean_box(0));
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; uint8_t v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = lean_unbox(v_a_979_);
lean_dec(v_a_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_982_; 
lean_dec(v_a_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_snd_958_);
lean_ctor_set(v___x_955_, 0, v_fst_957_);
v___x_982_ = v___x_955_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_fst_957_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_snd_958_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_982_);
lean_ctor_set(v___x_947_, 0, v_fst_953_);
v___x_984_ = v___x_947_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_953_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
v_a_964_ = v___x_984_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v_self_987_; lean_object* v___x_988_; 
v_self_987_ = lean_ctor_get(v_a_952_, 0);
lean_inc_ref(v_self_987_);
lean_dec(v_a_952_);
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_958_, v_self_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_989_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_932_, v_snd_958_, v_self_987_, v_fst_957_, v_fst_953_);
lean_inc_n(v___x_989_, 2);
v___x_990_ = l_Rat_ofInt(v___x_989_);
v___x_991_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_932_, v_self_987_, v___x_990_, v_snd_958_);
v___x_992_ = lean_box(0);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_957_, v___x_989_, v___x_992_);
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_995_ = lean_int_add(v___x_989_, v___x_994_);
lean_dec(v___x_989_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_991_);
lean_ctor_set(v___x_955_, 0, v___x_993_);
v___x_997_ = v___x_955_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_991_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_997_);
lean_ctor_set(v___x_947_, 0, v___x_995_);
v___x_999_ = v___x_947_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
v_a_964_ = v___x_999_;
goto v___jp_963_;
}
}
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref_known(v___x_988_, 1);
lean_dec_ref(v_self_987_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_snd_958_);
lean_ctor_set(v___x_955_, 0, v_fst_957_);
v___x_1003_ = v___x_955_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_fst_957_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_snd_958_);
v___x_1003_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_1003_);
lean_ctor_set(v___x_947_, 0, v_fst_953_);
v___x_1005_ = v___x_947_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_fst_953_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v_a_964_ = v___x_1005_;
goto v___jp_963_;
}
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_del_object(v___x_960_);
lean_dec(v_snd_958_);
lean_dec(v_fst_957_);
lean_del_object(v___x_955_);
lean_dec(v_fst_953_);
lean_dec(v_a_952_);
lean_del_object(v___x_947_);
lean_dec_ref(v_isTarget_933_);
v_a_1008_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_978_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_978_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
v___jp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_964_);
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_966_ = v___x_960_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_a_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((size_t)1ULL);
v___x_968_ = lean_usize_add(v_i_936_, v___x_967_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_932_, v_isTarget_933_, v_as_934_, v_sz_935_, v___x_968_, v___x_966_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_969_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_del_object(v___x_947_);
lean_dec(v_snd_945_);
lean_dec_ref(v_isTarget_933_);
v_a_1019_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_950_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_950_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1029_, lean_object* v_isTarget_1030_, lean_object* v_as_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
size_t v_sz_boxed_1040_; size_t v_i_boxed_1041_; lean_object* v_res_1042_; 
v_sz_boxed_1040_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1041_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1029_, v_isTarget_1030_, v_as_1031_, v_sz_boxed_1040_, v_i_boxed_1041_, v_b_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_as_1031_);
lean_dec_ref(v_goal_1029_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1043_, lean_object* v_isTarget_1044_, lean_object* v_as_1045_, size_t v_sz_1046_, size_t v_i_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v___x_1054_; 
v___x_1054_ = lean_usize_dec_lt(v_i_1047_, v_sz_1046_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v_isTarget_1044_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1048_);
return v___x_1055_;
}
else
{
lean_object* v_snd_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1138_; 
v_snd_1056_ = lean_ctor_get(v_b_1048_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_b_1048_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_b_1048_, 0);
lean_dec(v_unused_1139_);
v___x_1058_ = v_b_1048_;
v_isShared_1059_ = v_isSharedCheck_1138_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_snd_1056_);
lean_dec(v_b_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1138_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_array_uget_borrowed(v_as_1045_, v_i_1047_);
lean_inc(v_a_1060_);
v___x_1061_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1043_, v_a_1060_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_snd_1062_; lean_object* v_a_1063_; lean_object* v_fst_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1128_; 
v_snd_1062_ = lean_ctor_get(v_snd_1056_, 1);
lean_inc(v_snd_1062_);
v_a_1063_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1061_, 1);
v_fst_1064_ = lean_ctor_get(v_snd_1056_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_snd_1056_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_snd_1056_, 1);
lean_dec(v_unused_1129_);
v___x_1066_ = v_snd_1056_;
v_isShared_1067_ = v_isSharedCheck_1128_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_fst_1064_);
lean_dec(v_snd_1056_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1128_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1127_; 
v_fst_1068_ = lean_ctor_get(v_snd_1062_, 0);
v_snd_1069_ = lean_ctor_get(v_snd_1062_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_snd_1062_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1071_ = v_snd_1062_;
v_isShared_1072_ = v_isSharedCheck_1127_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_snd_1069_);
lean_inc(v_fst_1068_);
lean_dec(v_snd_1062_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1127_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v_a_1075_; uint8_t v___x_1082_; 
v___x_1073_ = lean_box(0);
v___x_1082_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1063_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_a_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_snd_1069_);
lean_ctor_set(v___x_1066_, 0, v_fst_1068_);
v___x_1084_ = v___x_1066_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_snd_1069_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1084_);
lean_ctor_set(v___x_1058_, 0, v_fst_1064_);
v___x_1086_ = v___x_1058_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_fst_1064_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v_a_1075_ = v___x_1086_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v___x_1089_; 
lean_inc_ref(v_isTarget_1044_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v_a_1063_);
v___x_1089_ = lean_apply_6(v_isTarget_1044_, v_a_1063_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, lean_box(0));
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; uint8_t v___x_1091_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_unbox(v_a_1090_);
lean_dec(v_a_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v_a_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_snd_1069_);
lean_ctor_set(v___x_1066_, 0, v_fst_1068_);
v___x_1093_ = v___x_1066_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_snd_1069_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1093_);
lean_ctor_set(v___x_1058_, 0, v_fst_1064_);
v___x_1095_ = v___x_1058_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fst_1064_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v_a_1075_ = v___x_1095_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v_self_1098_; lean_object* v___x_1099_; 
v_self_1098_ = lean_ctor_get(v_a_1063_, 0);
lean_inc_ref(v_self_1098_);
lean_dec(v_a_1063_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1069_, v_self_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1043_, v_snd_1069_, v_self_1098_, v_fst_1068_, v_fst_1064_);
lean_inc_n(v___x_1100_, 2);
v___x_1101_ = l_Rat_ofInt(v___x_1100_);
v___x_1102_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1043_, v_self_1098_, v___x_1101_, v_snd_1069_);
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1068_, v___x_1100_, v___x_1103_);
v___x_1105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1106_ = lean_int_add(v___x_1100_, v___x_1105_);
lean_dec(v___x_1100_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1102_);
lean_ctor_set(v___x_1066_, 0, v___x_1104_);
v___x_1108_ = v___x_1066_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1102_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1108_);
lean_ctor_set(v___x_1058_, 0, v___x_1106_);
v___x_1110_ = v___x_1058_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v_a_1075_ = v___x_1110_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec_ref_known(v___x_1099_, 1);
lean_dec_ref(v_self_1098_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_snd_1069_);
lean_ctor_set(v___x_1066_, 0, v_fst_1068_);
v___x_1114_ = v___x_1066_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_fst_1068_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_snd_1069_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1114_);
lean_ctor_set(v___x_1058_, 0, v_fst_1064_);
v___x_1116_ = v___x_1058_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_fst_1064_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v_a_1075_ = v___x_1116_;
goto v___jp_1074_;
}
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_del_object(v___x_1071_);
lean_dec(v_snd_1069_);
lean_dec(v_fst_1068_);
lean_del_object(v___x_1066_);
lean_dec(v_fst_1064_);
lean_dec(v_a_1063_);
lean_del_object(v___x_1058_);
lean_dec_ref(v_isTarget_1044_);
v_a_1119_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1089_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1089_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
v___jp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_a_1075_);
lean_ctor_set(v___x_1071_, 0, v___x_1073_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_a_1075_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
size_t v___x_1078_; size_t v___x_1079_; 
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1047_, v___x_1078_);
v_i_1047_ = v___x_1079_;
v_b_1048_ = v___x_1077_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_del_object(v___x_1058_);
lean_dec(v_snd_1056_);
lean_dec_ref(v_isTarget_1044_);
v_a_1130_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1061_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1061_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1140_, lean_object* v_isTarget_1141_, lean_object* v_as_1142_, lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
size_t v_sz_boxed_1151_; size_t v_i_boxed_1152_; lean_object* v_res_1153_; 
v_sz_boxed_1151_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1152_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1140_, v_isTarget_1141_, v_as_1142_, v_sz_boxed_1151_, v_i_boxed_1152_, v_b_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec_ref(v_as_1142_);
lean_dec_ref(v_goal_1140_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1154_, lean_object* v_isTarget_1155_, lean_object* v_as_1156_, size_t v_sz_1157_, size_t v_i_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_usize_dec_lt(v_i_1158_, v_sz_1157_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_isTarget_1155_);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_b_1159_);
return v___x_1166_;
}
else
{
lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1249_; 
v_snd_1167_ = lean_ctor_get(v_b_1159_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_b_1159_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v_b_1159_, 0);
lean_dec(v_unused_1250_);
v___x_1169_ = v_b_1159_;
v_isShared_1170_ = v_isSharedCheck_1249_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_dec(v_b_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1249_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_array_uget_borrowed(v_as_1156_, v_i_1158_);
lean_inc(v_a_1171_);
v___x_1172_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1154_, v_a_1171_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_snd_1173_; lean_object* v_a_1174_; lean_object* v_fst_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1239_; 
v_snd_1173_ = lean_ctor_get(v_snd_1167_, 1);
lean_inc(v_snd_1173_);
v_a_1174_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1172_, 1);
v_fst_1175_ = lean_ctor_get(v_snd_1167_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_snd_1167_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_snd_1167_, 1);
lean_dec(v_unused_1240_);
v___x_1177_ = v_snd_1167_;
v_isShared_1178_ = v_isSharedCheck_1239_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_fst_1175_);
lean_dec(v_snd_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1239_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1238_; 
v_fst_1179_ = lean_ctor_get(v_snd_1173_, 0);
v_snd_1180_ = lean_ctor_get(v_snd_1173_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_snd_1173_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1182_ = v_snd_1173_;
v_isShared_1183_ = v_isSharedCheck_1238_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_snd_1173_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1238_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v_a_1186_; uint8_t v___x_1193_; 
v___x_1184_ = lean_box(0);
v___x_1193_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1174_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v_a_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_snd_1180_);
lean_ctor_set(v___x_1177_, 0, v_fst_1179_);
v___x_1195_ = v___x_1177_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_snd_1180_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1195_);
lean_ctor_set(v___x_1169_, 0, v_fst_1175_);
v___x_1197_ = v___x_1169_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_fst_1175_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v_a_1186_ = v___x_1197_;
goto v___jp_1185_;
}
}
}
else
{
lean_object* v___x_1200_; 
lean_inc_ref(v_isTarget_1155_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v_a_1174_);
v___x_1200_ = lean_apply_6(v_isTarget_1155_, v_a_1174_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, lean_box(0));
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; uint8_t v___x_1202_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = lean_unbox(v_a_1201_);
lean_dec(v_a_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; 
lean_dec(v_a_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_snd_1180_);
lean_ctor_set(v___x_1177_, 0, v_fst_1179_);
v___x_1204_ = v___x_1177_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_snd_1180_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1204_);
lean_ctor_set(v___x_1169_, 0, v_fst_1175_);
v___x_1206_ = v___x_1169_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_fst_1175_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v_a_1186_ = v___x_1206_;
goto v___jp_1185_;
}
}
}
else
{
lean_object* v_self_1209_; lean_object* v___x_1210_; 
v_self_1209_ = lean_ctor_get(v_a_1174_, 0);
lean_inc_ref(v_self_1209_);
lean_dec(v_a_1174_);
v___x_1210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1180_, v_self_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1211_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1154_, v_snd_1180_, v_self_1209_, v_fst_1179_, v_fst_1175_);
lean_inc_n(v___x_1211_, 2);
v___x_1212_ = l_Rat_ofInt(v___x_1211_);
v___x_1213_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1154_, v_self_1209_, v___x_1212_, v_snd_1180_);
v___x_1214_ = lean_box(0);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1179_, v___x_1211_, v___x_1214_);
v___x_1216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1217_ = lean_int_add(v___x_1211_, v___x_1216_);
lean_dec(v___x_1211_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1213_);
lean_ctor_set(v___x_1177_, 0, v___x_1215_);
v___x_1219_ = v___x_1177_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1213_);
v___x_1219_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1219_);
lean_ctor_set(v___x_1169_, 0, v___x_1217_);
v___x_1221_ = v___x_1169_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_a_1186_ = v___x_1221_;
goto v___jp_1185_;
}
}
}
else
{
lean_object* v___x_1225_; 
lean_dec_ref_known(v___x_1210_, 1);
lean_dec_ref(v_self_1209_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_snd_1180_);
lean_ctor_set(v___x_1177_, 0, v_fst_1179_);
v___x_1225_ = v___x_1177_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_snd_1180_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1225_);
lean_ctor_set(v___x_1169_, 0, v_fst_1175_);
v___x_1227_ = v___x_1169_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_fst_1175_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v_a_1186_ = v___x_1227_;
goto v___jp_1185_;
}
}
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_del_object(v___x_1177_);
lean_dec(v_fst_1175_);
lean_dec(v_a_1174_);
lean_del_object(v___x_1169_);
lean_dec_ref(v_isTarget_1155_);
v_a_1230_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1200_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1200_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
v___jp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_a_1186_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1188_ = v___x_1182_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1186_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_add(v_i_1158_, v___x_1189_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1154_, v_isTarget_1155_, v_as_1156_, v_sz_1157_, v___x_1190_, v___x_1188_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1169_);
lean_dec(v_snd_1167_);
lean_dec_ref(v_isTarget_1155_);
v_a_1241_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1172_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1172_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1251_, lean_object* v_isTarget_1252_, lean_object* v_as_1253_, lean_object* v_sz_1254_, lean_object* v_i_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
size_t v_sz_boxed_1262_; size_t v_i_boxed_1263_; lean_object* v_res_1264_; 
v_sz_boxed_1262_ = lean_unbox_usize(v_sz_1254_);
lean_dec(v_sz_1254_);
v_i_boxed_1263_ = lean_unbox_usize(v_i_1255_);
lean_dec(v_i_1255_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1251_, v_isTarget_1252_, v_as_1253_, v_sz_boxed_1262_, v_i_boxed_1263_, v_b_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v_as_1253_);
lean_dec_ref(v_goal_1251_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1265_, lean_object* v_goal_1266_, lean_object* v_isTarget_1267_, lean_object* v_n_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
if (lean_obj_tag(v_n_1268_) == 0)
{
lean_object* v_cs_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; size_t v_sz_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v_cs_1275_ = lean_ctor_get(v_n_1268_, 0);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_b_1269_);
v_sz_1278_ = lean_array_size(v_cs_1275_);
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1265_, v_goal_1266_, v_isTarget_1267_, v_cs_1275_, v_sz_1278_, v___x_1279_, v___x_1277_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1295_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_fst_1285_; 
v_fst_1285_ = lean_ctor_get(v_a_1281_, 0);
if (lean_obj_tag(v_fst_1285_) == 0)
{
lean_object* v_snd_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v_snd_1286_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1286_);
lean_dec(v_a_1281_);
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_snd_1286_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1287_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; 
lean_inc_ref(v_fst_1285_);
lean_dec(v_a_1281_);
v_val_1291_ = lean_ctor_get(v_fst_1285_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v_fst_1285_, 1);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_val_1291_);
v___x_1293_ = v___x_1283_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_val_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1280_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1280_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_vs_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; size_t v_sz_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v_vs_1304_ = lean_ctor_get(v_n_1268_, 0);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_b_1269_);
v_sz_1307_ = lean_array_size(v_vs_1304_);
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1266_, v_isTarget_1267_, v_vs_1304_, v_sz_1307_, v___x_1308_, v___x_1306_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1324_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1324_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; 
v_fst_1314_ = lean_ctor_get(v_a_1310_, 0);
if (lean_obj_tag(v_fst_1314_) == 0)
{
lean_object* v_snd_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
v_snd_1315_ = lean_ctor_get(v_a_1310_, 1);
lean_inc(v_snd_1315_);
lean_dec(v_a_1310_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_snd_1315_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1316_);
v___x_1318_ = v___x_1312_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v_val_1320_; lean_object* v___x_1322_; 
lean_inc_ref(v_fst_1314_);
lean_dec(v_a_1310_);
v_val_1320_ = lean_ctor_get(v_fst_1314_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v_fst_1314_, 1);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_val_1320_);
v___x_1322_ = v___x_1312_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_val_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1309_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1309_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1333_, lean_object* v_goal_1334_, lean_object* v_isTarget_1335_, lean_object* v_as_1336_, size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_b_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v_isTarget_1335_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_b_1339_);
return v___x_1346_;
}
else
{
lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1381_; 
v_snd_1347_ = lean_ctor_get(v_b_1339_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_b_1339_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_b_1339_, 0);
lean_dec(v_unused_1382_);
v___x_1349_ = v_b_1339_;
v_isShared_1350_ = v_isSharedCheck_1381_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_dec(v_b_1339_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1381_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_array_uget_borrowed(v_as_1336_, v_i_1338_);
lean_inc(v_snd_1347_);
lean_inc_ref(v_isTarget_1335_);
v___x_1352_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1333_, v_goal_1334_, v_isTarget_1335_, v_a_1351_, v_snd_1347_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1372_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1372_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1372_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
if (lean_obj_tag(v_a_1353_) == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_dec_ref(v_isTarget_1335_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1353_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1357_);
v___x_1359_ = v___x_1349_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_snd_1347_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_del_object(v___x_1355_);
lean_dec(v_snd_1347_);
v_a_1364_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v_a_1353_, 1);
v___x_1365_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v_a_1364_);
lean_ctor_set(v___x_1349_, 0, v___x_1365_);
v___x_1367_ = v___x_1349_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1364_);
v___x_1367_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
size_t v___x_1368_; size_t v___x_1369_; 
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_add(v_i_1338_, v___x_1368_);
v_i_1338_ = v___x_1369_;
v_b_1339_ = v___x_1367_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_del_object(v___x_1349_);
lean_dec(v_snd_1347_);
lean_dec_ref(v_isTarget_1335_);
v_a_1373_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1352_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1352_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1383_, lean_object* v_goal_1384_, lean_object* v_isTarget_1385_, lean_object* v_as_1386_, lean_object* v_sz_1387_, lean_object* v_i_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1387_);
lean_dec(v_sz_1387_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1383_, v_goal_1384_, v_isTarget_1385_, v_as_1386_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec_ref(v_as_1386_);
lean_dec_ref(v_goal_1384_);
lean_dec_ref(v_init_1383_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1398_, lean_object* v_goal_1399_, lean_object* v_isTarget_1400_, lean_object* v_n_1401_, lean_object* v_b_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1398_, v_goal_1399_, v_isTarget_1400_, v_n_1401_, v_b_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v_n_1401_);
lean_dec_ref(v_goal_1399_);
lean_dec_ref(v_init_1398_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1409_, lean_object* v_isTarget_1410_, lean_object* v_t_1411_, lean_object* v_init_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_root_1418_; lean_object* v_tail_1419_; lean_object* v___x_1420_; 
v_root_1418_ = lean_ctor_get(v_t_1411_, 0);
v_tail_1419_ = lean_ctor_get(v_t_1411_, 1);
lean_inc_ref(v_isTarget_1410_);
lean_inc_ref(v_init_1412_);
v___x_1420_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1412_, v_goal_1409_, v_isTarget_1410_, v_root_1418_, v_init_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec_ref(v_init_1412_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1457_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1457_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1457_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
if (lean_obj_tag(v_a_1421_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; 
lean_dec_ref(v_isTarget_1410_);
v_a_1425_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v_a_1421_, 1);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_a_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
lean_del_object(v___x_1423_);
v_a_1429_ = lean_ctor_get(v_a_1421_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v_a_1421_, 1);
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_a_1429_);
v_sz_1432_ = lean_array_size(v_tail_1419_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1409_, v_isTarget_1410_, v_tail_1419_, v_sz_1432_, v___x_1433_, v___x_1431_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1448_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1448_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_fst_1439_; 
v_fst_1439_ = lean_ctor_get(v_a_1435_, 0);
if (lean_obj_tag(v_fst_1439_) == 0)
{
lean_object* v_snd_1440_; lean_object* v___x_1442_; 
v_snd_1440_ = lean_ctor_get(v_a_1435_, 1);
lean_inc(v_snd_1440_);
lean_dec(v_a_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_snd_1440_);
v___x_1442_ = v___x_1437_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_snd_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1446_; 
lean_inc_ref(v_fst_1439_);
lean_dec(v_a_1435_);
v_val_1444_ = lean_ctor_get(v_fst_1439_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v_fst_1439_, 1);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v_val_1444_);
v___x_1446_ = v___x_1437_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_val_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1434_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1434_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_isTarget_1410_);
v_a_1458_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1420_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1420_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1466_, lean_object* v_isTarget_1467_, lean_object* v_t_1468_, lean_object* v_init_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1466_, v_isTarget_1467_, v_t_1468_, v_init_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec_ref(v_t_1468_);
lean_dec_ref(v_goal_1466_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
if (lean_obj_tag(v_a_1476_) == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1477_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
else
{
lean_object* v_value_1481_; lean_object* v_tail_1482_; lean_object* v_num_1483_; lean_object* v_den_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_value_1481_ = lean_ctor_get(v_a_1476_, 1);
lean_inc(v_value_1481_);
v_tail_1482_ = lean_ctor_get(v_a_1476_, 2);
lean_inc(v_tail_1482_);
lean_dec_ref_known(v_a_1476_, 3);
v_num_1483_ = lean_ctor_get(v_value_1481_, 0);
lean_inc(v_num_1483_);
v_den_1484_ = lean_ctor_get(v_value_1481_, 1);
lean_inc(v_den_1484_);
lean_dec(v_value_1481_);
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_dec_eq(v_den_1484_, v___x_1485_);
lean_dec(v_den_1484_);
if (v___x_1486_ == 0)
{
lean_dec(v_num_1483_);
v_a_1476_ = v_tail_1482_;
goto _start;
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1477_, v_num_1483_, v___x_1488_);
v_a_1476_ = v_tail_1482_;
v_a_1477_ = v___x_1489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1491_, v_a_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_b_1498_);
return v___x_1505_;
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_array_uget_borrowed(v_as_1495_, v_i_1497_);
lean_inc(v_a_1506_);
v___x_1507_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1506_, v_b_1498_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1520_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; 
v_a_1512_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v_a_1508_, 1);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_a_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
else
{
lean_object* v_a_1516_; size_t v___x_1517_; size_t v___x_1518_; 
lean_del_object(v___x_1510_);
v_a_1516_ = lean_ctor_get(v_a_1508_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v_a_1508_, 1);
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1497_, v___x_1517_);
v_i_1497_ = v___x_1518_;
v_b_1498_ = v_a_1516_;
goto _start;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
v_a_1521_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1507_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1507_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1529_, lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
size_t v_sz_boxed_1538_; size_t v_i_boxed_1539_; lean_object* v_res_1540_; 
v_sz_boxed_1538_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1539_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1529_, v_sz_boxed_1538_, v_i_boxed_1539_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_as_1529_);
return v_res_1540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_unsigned_to_nat(16u);
v___x_1543_ = lean_mk_array(v___x_1542_, v___x_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_used_1546_; 
v___x_1544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1545_ = lean_unsigned_to_nat(0u);
v_used_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1546_, 0, v___x_1545_);
lean_ctor_set(v_used_1546_, 1, v___x_1544_);
return v_used_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1547_, lean_object* v_isTarget_1548_, lean_object* v_model_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_buckets_1555_; lean_object* v_used_1556_; size_t v_sz_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v_buckets_1555_ = lean_ctor_get(v_model_1549_, 1);
v_used_1556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1557_ = lean_array_size(v_buckets_1555_);
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1555_, v_sz_1557_, v___x_1558_, v_used_1556_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_toGoalState_1560_; lean_object* v_a_1561_; lean_object* v_exprs_1562_; lean_object* v_nextVal_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_toGoalState_1560_ = lean_ctor_get(v_goal_1547_, 0);
v_a_1561_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1559_, 1);
v_exprs_1562_ = lean_ctor_get(v_toGoalState_1560_, 2);
v_nextVal_1563_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1561_);
lean_ctor_set(v___x_1564_, 1, v_model_1549_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_nextVal_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1547_, v_isTarget_1548_, v_exprs_1562_, v___x_1565_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1576_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_snd_1571_; lean_object* v_snd_1572_; lean_object* v___x_1574_; 
v_snd_1571_ = lean_ctor_get(v_a_1567_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_a_1567_);
v_snd_1572_ = lean_ctor_get(v_snd_1571_, 1);
lean_inc(v_snd_1572_);
lean_dec(v_snd_1571_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_snd_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_snd_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1566_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1566_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_model_1549_);
lean_dec_ref(v_isTarget_1548_);
v_a_1585_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1559_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1559_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1593_, lean_object* v_isTarget_1594_, lean_object* v_model_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1593_, v_isTarget_1594_, v_model_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec_ref(v_goal_1593_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1602_, lean_object* v_m_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1603_, v_a_1604_, v_b_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1607_, v_a_1608_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1615_, v_a_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1623_, lean_object* v_data_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1626_, lean_object* v_i_1627_, lean_object* v_source_1628_, lean_object* v_target_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1627_, v_source_1628_, v_target_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1635_, lean_object* v_hi_1636_, lean_object* v_pivot_1637_, lean_object* v_as_1638_, lean_object* v_i_1639_, lean_object* v_k_1640_){
_start:
{
uint8_t v___y_1642_; uint8_t v___x_1651_; 
v___x_1651_ = lean_nat_dec_lt(v_k_1640_, v_hi_1636_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec(v_k_1640_);
v___x_1652_ = lean_array_fswap(v_as_1638_, v_i_1639_, v_hi_1636_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_i_1639_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v_fst_1655_; lean_object* v_fst_1656_; lean_object* v_g_u2081_1657_; lean_object* v_g_u2082_1658_; uint8_t v___x_1659_; 
v___x_1654_ = lean_array_fget_borrowed(v_as_1638_, v_k_1640_);
v_fst_1655_ = lean_ctor_get(v___x_1654_, 0);
v_fst_1656_ = lean_ctor_get(v_pivot_1637_, 0);
v_g_u2081_1657_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1635_, v_fst_1655_);
v_g_u2082_1658_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1635_, v_fst_1656_);
v___x_1659_ = lean_nat_dec_eq(v_g_u2081_1657_, v_g_u2082_1658_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_lt(v_g_u2081_1657_, v_g_u2082_1658_);
lean_dec(v_g_u2082_1658_);
lean_dec(v_g_u2081_1657_);
v___y_1642_ = v___x_1660_;
goto v___jp_1641_;
}
else
{
uint8_t v___x_1661_; 
lean_dec(v_g_u2082_1658_);
lean_dec(v_g_u2081_1657_);
v___x_1661_ = lean_expr_lt(v_fst_1655_, v_fst_1656_);
v___y_1642_ = v___x_1661_;
goto v___jp_1641_;
}
}
v___jp_1641_:
{
if (v___y_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_k_1640_, v___x_1643_);
lean_dec(v_k_1640_);
v_k_1640_ = v___x_1644_;
goto _start;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_array_fswap(v_as_1638_, v_i_1639_, v_k_1640_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_i_1639_, v___x_1647_);
lean_dec(v_i_1639_);
v___x_1649_ = lean_nat_add(v_k_1640_, v___x_1647_);
lean_dec(v_k_1640_);
v_as_1638_ = v___x_1646_;
v_i_1639_ = v___x_1648_;
v_k_1640_ = v___x_1649_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1662_, lean_object* v_hi_1663_, lean_object* v_pivot_1664_, lean_object* v_as_1665_, lean_object* v_i_1666_, lean_object* v_k_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1662_, v_hi_1663_, v_pivot_1664_, v_as_1665_, v_i_1666_, v_k_1667_);
lean_dec_ref(v_pivot_1664_);
lean_dec(v_hi_1663_);
lean_dec_ref(v_goal_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v_fst_1672_; lean_object* v_fst_1673_; lean_object* v_g_u2081_1674_; lean_object* v_g_u2082_1675_; uint8_t v___x_1676_; 
v_fst_1672_ = lean_ctor_get(v_x_1670_, 0);
v_fst_1673_ = lean_ctor_get(v_x_1671_, 0);
v_g_u2081_1674_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1669_, v_fst_1672_);
v_g_u2082_1675_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1669_, v_fst_1673_);
v___x_1676_ = lean_nat_dec_eq(v_g_u2081_1674_, v_g_u2082_1675_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_nat_dec_lt(v_g_u2081_1674_, v_g_u2082_1675_);
lean_dec(v_g_u2082_1675_);
lean_dec(v_g_u2081_1674_);
return v___x_1677_;
}
else
{
uint8_t v___x_1678_; 
lean_dec(v_g_u2082_1675_);
lean_dec(v_g_u2081_1674_);
v___x_1678_ = lean_expr_lt(v_fst_1672_, v_fst_1673_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
uint8_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1679_, v_x_1680_, v_x_1681_);
lean_dec_ref(v_x_1681_);
lean_dec_ref(v_x_1680_);
lean_dec_ref(v_goal_1679_);
v_r_1683_ = lean_box(v_res_1682_);
return v_r_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1684_, lean_object* v_n_1685_, lean_object* v_as_1686_, lean_object* v_lo_1687_, lean_object* v_hi_1688_){
_start:
{
lean_object* v___y_1690_; uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_lt(v_lo_1687_, v_hi_1688_);
if (v___x_1700_ == 0)
{
lean_dec(v_lo_1687_);
return v_as_1686_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_mid_1703_; lean_object* v___y_1705_; lean_object* v___y_1711_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1701_ = lean_nat_add(v_lo_1687_, v_hi_1688_);
v___x_1702_ = lean_unsigned_to_nat(1u);
v_mid_1703_ = lean_nat_shiftr(v___x_1701_, v___x_1702_);
lean_dec(v___x_1701_);
v___x_1716_ = lean_array_fget_borrowed(v_as_1686_, v_mid_1703_);
v___x_1717_ = lean_array_fget_borrowed(v_as_1686_, v_lo_1687_);
v___x_1718_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1684_, v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
v___y_1711_ = v_as_1686_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_array_fswap(v_as_1686_, v_lo_1687_, v_mid_1703_);
v___y_1711_ = v___x_1719_;
goto v___jp_1710_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1706_ = lean_array_fget_borrowed(v___y_1705_, v_mid_1703_);
v___x_1707_ = lean_array_fget_borrowed(v___y_1705_, v_hi_1688_);
v___x_1708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1684_, v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_dec(v_mid_1703_);
v___y_1690_ = v___y_1705_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_array_fswap(v___y_1705_, v_mid_1703_, v_hi_1688_);
lean_dec(v_mid_1703_);
v___y_1690_ = v___x_1709_;
goto v___jp_1689_;
}
}
v___jp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = lean_array_fget_borrowed(v___y_1711_, v_hi_1688_);
v___x_1713_ = lean_array_fget_borrowed(v___y_1711_, v_lo_1687_);
v___x_1714_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1684_, v___x_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
v___y_1705_ = v___y_1711_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_array_fswap(v___y_1711_, v_lo_1687_, v_hi_1688_);
v___y_1705_ = v___x_1715_;
goto v___jp_1704_;
}
}
}
v___jp_1689_:
{
lean_object* v_pivot_1691_; lean_object* v___x_1692_; lean_object* v_fst_1693_; lean_object* v_snd_1694_; uint8_t v___x_1695_; 
v_pivot_1691_ = lean_array_fget(v___y_1690_, v_hi_1688_);
lean_inc_n(v_lo_1687_, 2);
v___x_1692_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1684_, v_hi_1688_, v_pivot_1691_, v___y_1690_, v_lo_1687_, v_lo_1687_);
lean_dec(v_pivot_1691_);
v_fst_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_fst_1693_);
v_snd_1694_ = lean_ctor_get(v___x_1692_, 1);
lean_inc(v_snd_1694_);
lean_dec_ref(v___x_1692_);
v___x_1695_ = lean_nat_dec_le(v_hi_1688_, v_fst_1693_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1684_, v_n_1685_, v_snd_1694_, v_lo_1687_, v_fst_1693_);
v___x_1697_ = lean_unsigned_to_nat(1u);
v___x_1698_ = lean_nat_add(v_fst_1693_, v___x_1697_);
lean_dec(v_fst_1693_);
v_as_1686_ = v___x_1696_;
v_lo_1687_ = v___x_1698_;
goto _start;
}
else
{
lean_dec(v_fst_1693_);
lean_dec(v_lo_1687_);
return v_snd_1694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1720_, lean_object* v_n_1721_, lean_object* v_as_1722_, lean_object* v_lo_1723_, lean_object* v_hi_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1720_, v_n_1721_, v_as_1722_, v_lo_1723_, v_hi_1724_);
lean_dec(v_hi_1724_);
lean_dec(v_n_1721_);
lean_dec_ref(v_goal_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1726_, lean_object* v_m_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1728_ = lean_array_get_size(v_m_1727_);
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_nat_dec_eq(v___x_1728_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___y_1734_; uint8_t v___x_1738_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_sub(v___x_1728_, v___x_1731_);
v___x_1738_ = lean_nat_dec_le(v___x_1729_, v___x_1732_);
if (v___x_1738_ == 0)
{
lean_inc(v___x_1732_);
v___y_1734_ = v___x_1732_;
goto v___jp_1733_;
}
else
{
v___y_1734_ = v___x_1729_;
goto v___jp_1733_;
}
v___jp_1733_:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_le(v___y_1734_, v___x_1732_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v___x_1732_);
lean_inc(v___y_1734_);
v___x_1736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1726_, v___x_1728_, v_m_1727_, v___y_1734_, v___y_1734_);
lean_dec(v___y_1734_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1726_, v___x_1728_, v_m_1727_, v___y_1734_, v___x_1732_);
lean_dec(v___x_1732_);
return v___x_1737_;
}
}
}
else
{
return v_m_1727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1739_, lean_object* v_m_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1739_, v_m_1740_);
lean_dec_ref(v_goal_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1742_, lean_object* v_n_1743_, lean_object* v_as_1744_, lean_object* v_lo_1745_, lean_object* v_hi_1746_, lean_object* v_w_1747_, lean_object* v_hlo_1748_, lean_object* v_hhi_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1742_, v_n_1743_, v_as_1744_, v_lo_1745_, v_hi_1746_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1751_, lean_object* v_n_1752_, lean_object* v_as_1753_, lean_object* v_lo_1754_, lean_object* v_hi_1755_, lean_object* v_w_1756_, lean_object* v_hlo_1757_, lean_object* v_hhi_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1751_, v_n_1752_, v_as_1753_, v_lo_1754_, v_hi_1755_, v_w_1756_, v_hlo_1757_, v_hhi_1758_);
lean_dec(v_hi_1755_);
lean_dec(v_n_1752_);
lean_dec_ref(v_goal_1751_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1760_, lean_object* v_n_1761_, lean_object* v_lo_1762_, lean_object* v_hi_1763_, lean_object* v_hhi_1764_, lean_object* v_pivot_1765_, lean_object* v_as_1766_, lean_object* v_i_1767_, lean_object* v_k_1768_, lean_object* v_ilo_1769_, lean_object* v_ik_1770_, lean_object* v_w_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1760_, v_hi_1763_, v_pivot_1765_, v_as_1766_, v_i_1767_, v_k_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1773_, lean_object* v_n_1774_, lean_object* v_lo_1775_, lean_object* v_hi_1776_, lean_object* v_hhi_1777_, lean_object* v_pivot_1778_, lean_object* v_as_1779_, lean_object* v_i_1780_, lean_object* v_k_1781_, lean_object* v_ilo_1782_, lean_object* v_ik_1783_, lean_object* v_w_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1773_, v_n_1774_, v_lo_1775_, v_hi_1776_, v_hhi_1777_, v_pivot_1778_, v_as_1779_, v_i_1780_, v_k_1781_, v_ilo_1782_, v_ik_1783_, v_w_1784_);
lean_dec_ref(v_pivot_1778_);
lean_dec(v_hi_1776_);
lean_dec(v_lo_1775_);
lean_dec(v_n_1774_);
lean_dec_ref(v_goal_1773_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
if (lean_obj_tag(v_a_1786_) == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1787_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
else
{
lean_object* v_key_1791_; lean_object* v_value_1792_; lean_object* v_tail_1793_; uint8_t v___x_1794_; 
v_key_1791_ = lean_ctor_get(v_a_1786_, 0);
lean_inc_n(v_key_1791_, 2);
v_value_1792_ = lean_ctor_get(v_a_1786_, 1);
lean_inc(v_value_1792_);
v_tail_1793_ = lean_ctor_get(v_a_1786_, 2);
lean_inc(v_tail_1793_);
lean_dec_ref_known(v_a_1786_, 3);
v___x_1794_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1791_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_key_1791_);
lean_ctor_set(v___x_1795_, 1, v_value_1792_);
v___x_1796_ = lean_array_push(v_a_1787_, v___x_1795_);
v_a_1786_ = v_tail_1793_;
v_a_1787_ = v___x_1796_;
goto _start;
}
else
{
lean_dec(v_value_1792_);
lean_dec(v_key_1791_);
v_a_1786_ = v_tail_1793_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1799_, v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1803_, size_t v_sz_1804_, size_t v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_usize_dec_lt(v_i_1805_, v_sz_1804_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_b_1806_);
return v___x_1813_;
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_array_uget_borrowed(v_as_1803_, v_i_1805_);
lean_inc(v_a_1814_);
v___x_1815_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1814_, v_b_1806_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1828_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1828_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_a_1816_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; 
v_a_1820_ = lean_ctor_get(v_a_1816_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v_a_1816_, 1);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_a_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
lean_object* v_a_1824_; size_t v___x_1825_; size_t v___x_1826_; 
lean_del_object(v___x_1818_);
v_a_1824_ = lean_ctor_get(v_a_1816_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v_a_1816_, 1);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_add(v_i_1805_, v___x_1825_);
v_i_1805_ = v___x_1826_;
v_b_1806_ = v_a_1824_;
goto _start;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1815_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1815_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1837_, lean_object* v_sz_1838_, lean_object* v_i_1839_, lean_object* v_b_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; lean_object* v_res_1848_; 
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1838_);
lean_dec(v_sz_1838_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1839_);
lean_dec(v_i_1839_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1837_, v_sz_boxed_1846_, v_i_boxed_1847_, v_b_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_as_1837_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1851_, lean_object* v_isTarget_1852_, lean_object* v_model_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1851_, v_isTarget_1852_, v_model_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v_buckets_1861_; lean_object* v___x_1862_; size_t v_sz_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v_buckets_1861_ = lean_ctor_get(v_a_1860_, 1);
lean_inc_ref(v_buckets_1861_);
lean_dec(v_a_1860_);
v___x_1862_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1863_ = lean_array_size(v_buckets_1861_);
v___x_1864_ = ((size_t)0ULL);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1861_, v_sz_1863_, v___x_1864_, v___x_1862_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec_ref(v_buckets_1861_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1851_, v_a_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
return v___x_1865_;
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1859_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1859_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1883_, lean_object* v_isTarget_1884_, lean_object* v_model_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1883_, v_isTarget_1884_, v_model_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec_ref(v_goal_1883_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1892_, v_a_1893_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1900_, v_a_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v_env_1915_; lean_object* v___x_1916_; lean_object* v_toCold_1917_; lean_object* v_mctx_1918_; lean_object* v_lctx_1919_; lean_object* v_options_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1914_ = lean_st_ref_get(v___y_1912_);
v_env_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_env_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = lean_st_ref_get(v___y_1910_);
v_toCold_1917_ = lean_ctor_get(v___y_1911_, 0);
v_mctx_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_mctx_1918_);
lean_dec(v___x_1916_);
v_lctx_1919_ = lean_ctor_get(v___y_1909_, 2);
v_options_1920_ = lean_ctor_get(v_toCold_1917_, 2);
lean_inc_ref(v_options_1920_);
lean_inc_ref(v_lctx_1919_);
v___x_1921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1921_, 0, v_env_1915_);
lean_ctor_set(v___x_1921_, 1, v_mctx_1918_);
lean_ctor_set(v___x_1921_, 2, v_lctx_1919_);
lean_ctor_set(v___x_1921_, 3, v_options_1920_);
v___x_1922_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_msgData_1908_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1931_; double v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_float_of_nat(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_ref_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1989_; 
v_ref_1943_ = lean_ctor_get(v___y_1940_, 2);
v___x_1944_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1989_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1989_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v_traceState_1950_; lean_object* v_env_1951_; lean_object* v_nextMacroScope_1952_; lean_object* v_ngen_1953_; lean_object* v_auxDeclNGen_1954_; lean_object* v_cache_1955_; lean_object* v_messages_1956_; lean_object* v_infoState_1957_; lean_object* v_snapshotTasks_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1988_; 
v___x_1949_ = lean_st_ref_take(v___y_1941_);
v_traceState_1950_ = lean_ctor_get(v___x_1949_, 4);
v_env_1951_ = lean_ctor_get(v___x_1949_, 0);
v_nextMacroScope_1952_ = lean_ctor_get(v___x_1949_, 1);
v_ngen_1953_ = lean_ctor_get(v___x_1949_, 2);
v_auxDeclNGen_1954_ = lean_ctor_get(v___x_1949_, 3);
v_cache_1955_ = lean_ctor_get(v___x_1949_, 5);
v_messages_1956_ = lean_ctor_get(v___x_1949_, 6);
v_infoState_1957_ = lean_ctor_get(v___x_1949_, 7);
v_snapshotTasks_1958_ = lean_ctor_get(v___x_1949_, 8);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1960_ = v___x_1949_;
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snapshotTasks_1958_);
lean_inc(v_infoState_1957_);
lean_inc(v_messages_1956_);
lean_inc(v_cache_1955_);
lean_inc(v_traceState_1950_);
lean_inc(v_auxDeclNGen_1954_);
lean_inc(v_ngen_1953_);
lean_inc(v_nextMacroScope_1952_);
lean_inc(v_env_1951_);
lean_dec(v___x_1949_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint64_t v_tid_1962_; lean_object* v_traces_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1987_; 
v_tid_1962_ = lean_ctor_get_uint64(v_traceState_1950_, sizeof(void*)*1);
v_traces_1963_ = lean_ctor_get(v_traceState_1950_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_traceState_1950_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1965_ = v_traceState_1950_;
v_isShared_1966_ = v_isSharedCheck_1987_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_traces_1963_);
lean_dec(v_traceState_1950_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1987_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; double v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1969_ = 0;
v___x_1970_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1971_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1971_, 0, v_cls_1936_);
lean_ctor_set(v___x_1971_, 1, v___x_1967_);
lean_ctor_set(v___x_1971_, 2, v___x_1970_);
lean_ctor_set_float(v___x_1971_, sizeof(void*)*3, v___x_1968_);
lean_ctor_set_float(v___x_1971_, sizeof(void*)*3 + 8, v___x_1968_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*3 + 16, v___x_1969_);
v___x_1972_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1973_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v_a_1945_);
lean_ctor_set(v___x_1973_, 2, v___x_1972_);
lean_inc(v_ref_1943_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_ref_1943_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_PersistentArray_push___redArg(v_traces_1963_, v___x_1974_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1975_);
v___x_1977_ = v___x_1965_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1975_);
lean_ctor_set_uint64(v_reuseFailAlloc_1986_, sizeof(void*)*1, v_tid_1962_);
v___x_1977_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v___x_1977_);
v___x_1979_ = v___x_1960_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_env_1951_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_nextMacroScope_1952_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_ngen_1953_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_auxDeclNGen_1954_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1985_, 5, v_cache_1955_);
lean_ctor_set(v_reuseFailAlloc_1985_, 6, v_messages_1956_);
lean_ctor_set(v_reuseFailAlloc_1985_, 7, v_infoState_1957_);
lean_ctor_set(v_reuseFailAlloc_1985_, 8, v_snapshotTasks_1958_);
v___x_1979_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_st_ref_put(v___y_1941_, v___x_1979_);
v___x_1981_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1981_);
v___x_1983_ = v___x_1947_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1990_, lean_object* v_msg_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1990_, v_msg_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1997_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_2002_, lean_object* v_as_2003_, size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec(v_traceClass_2002_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_b_2006_);
return v___x_2013_;
}
else
{
lean_object* v_a_2014_; lean_object* v_snd_2015_; lean_object* v_fst_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2051_; 
v_a_2014_ = lean_array_uget(v_as_2003_, v_i_2005_);
v_snd_2015_ = lean_ctor_get(v_a_2014_, 1);
v_fst_2016_ = lean_ctor_get(v_a_2014_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2018_ = v_a_2014_;
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2016_);
lean_dec(v_a_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2051_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_num_2020_; lean_object* v_den_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2050_; 
v_num_2020_ = lean_ctor_get(v_snd_2015_, 0);
v_den_2021_ = lean_ctor_get(v_snd_2015_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_snd_2015_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2023_ = v_snd_2015_;
v_isShared_2024_ = v_isSharedCheck_2050_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_den_2021_);
lean_inc(v_num_2020_);
lean_dec(v_snd_2015_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2050_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2016_);
v___x_2027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 7);
lean_ctor_set(v___x_2023_, 1, v___x_2027_);
lean_ctor_set(v___x_2023_, 0, v___x_2026_);
v___x_2029_ = v___x_2023_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___y_2031_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_dec_eq(v_den_2021_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2043_ = l_Int_repr(v_num_2020_);
lean_dec(v_num_2020_);
v___x_2044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2045_ = lean_string_append(v___x_2043_, v___x_2044_);
v___x_2046_ = l_Nat_reprFast(v_den_2021_);
v___x_2047_ = lean_string_append(v___x_2045_, v___x_2046_);
lean_dec_ref(v___x_2046_);
v___y_2031_ = v___x_2047_;
goto v___jp_2030_;
}
else
{
lean_object* v___x_2048_; 
lean_dec(v_den_2021_);
v___x_2048_ = l_Int_repr(v_num_2020_);
lean_dec(v_num_2020_);
v___y_2031_ = v___x_2048_;
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___y_2031_);
v___x_2033_ = l_Lean_MessageData_ofFormat(v___x_2032_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 7);
lean_ctor_set(v___x_2018_, 1, v___x_2033_);
lean_ctor_set(v___x_2018_, 0, v___x_2029_);
v___x_2035_ = v___x_2018_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; 
lean_inc(v_traceClass_2002_);
v___x_2036_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_2002_, v___x_2035_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2036_) == 0)
{
size_t v___x_2037_; size_t v___x_2038_; 
lean_dec_ref_known(v___x_2036_, 1);
v___x_2037_ = ((size_t)1ULL);
v___x_2038_ = lean_usize_add(v_i_2005_, v___x_2037_);
v_i_2005_ = v___x_2038_;
v_b_2006_ = v___x_2025_;
goto _start;
}
else
{
lean_dec(v_traceClass_2002_);
return v___x_2036_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2052_, lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2052_, v_as_2053_, v_sz_boxed_2062_, v_i_boxed_2063_, v_b_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_as_2053_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2068_, lean_object* v_model_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_toCold_2078_; lean_object* v_options_2079_; uint8_t v_hasTrace_2080_; 
v_toCold_2078_ = lean_ctor_get(v_a_2072_, 0);
v_options_2079_ = lean_ctor_get(v_toCold_2078_, 2);
v_hasTrace_2080_ = lean_ctor_get_uint8(v_options_2079_, sizeof(void*)*1);
if (v_hasTrace_2080_ == 0)
{
lean_dec(v_traceClass_2068_);
goto v___jp_2075_;
}
else
{
lean_object* v_inheritedTraceOptions_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_inheritedTraceOptions_2081_ = lean_ctor_get(v_toCold_2078_, 11);
v___x_2082_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2068_);
v___x_2083_ = l_Lean_Name_append(v___x_2082_, v_traceClass_2068_);
v___x_2084_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2081_, v_options_2079_, v___x_2083_);
lean_dec(v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v_traceClass_2068_);
goto v___jp_2075_;
}
else
{
lean_object* v___x_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(0);
v_sz_2086_ = lean_array_size(v_model_2069_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2068_, v_model_2069_, v_sz_2086_, v___x_2087_, v___x_2085_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2088_, 0);
lean_dec(v_unused_2096_);
v___x_2090_ = v___x_2088_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v___x_2088_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2085_);
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2085_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
return v___x_2088_;
}
}
}
v___jp_2075_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2097_, lean_object* v_model_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2097_, v_model_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec_ref(v_model_2098_);
return v_res_2104_;
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
