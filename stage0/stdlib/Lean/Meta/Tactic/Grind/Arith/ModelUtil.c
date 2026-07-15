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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__9_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__10_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__12_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__16_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__18_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__19_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__21_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__22_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__24_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__25_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__27_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__28_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__30_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__31_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__33_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__34_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__38_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__39_value),LEAN_SCALAR_PTR_LITERAL(251, 249, 151, 171, 150, 156, 160, 34)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__41_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__42_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__37_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__44_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__45_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__46_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47_value;
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
v___y_129_ = v___x_131_;
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
v___y_94_ = v___x_125_;
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
size_t v_x_2623__boxed_193_; lean_object* v_res_194_; 
v_x_2623__boxed_193_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_194_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_190_, v_x_2623__boxed_193_, v_x_192_);
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
size_t v_x_2728__boxed_263_; lean_object* v_res_264_; 
v_x_2728__boxed_263_ = lean_unbox_usize(v_x_261_);
lean_dec(v_x_261_);
v_res_264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_259_, v_x_260_, v_x_2728__boxed_263_, v_x_262_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_462_){
_start:
{
uint8_t v___y_464_; uint8_t v___x_499_; 
lean_inc_ref(v_e_462_);
v___x_499_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_462_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; 
lean_inc_ref(v_e_462_);
v___x_500_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_462_);
v___y_464_ = v___x_500_;
goto v___jp_463_;
}
else
{
v___y_464_ = v___x_499_;
goto v___jp_463_;
}
v___jp_463_:
{
if (v___y_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_466_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5));
v___x_468_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8));
v___x_470_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11));
v___x_472_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14));
v___x_474_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17));
v___x_476_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20));
v___x_478_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23));
v___x_480_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26));
v___x_482_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29));
v___x_484_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32));
v___x_486_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_485_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_Expr_isIte(v_e_462_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; 
v___x_488_ = l_Lean_Expr_isDIte(v_e_462_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35));
v___x_490_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_492_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_494_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47));
v___x_496_ = l_Lean_Expr_isAppOf(v_e_462_, v___x_495_);
if (v___x_496_ == 0)
{
if (lean_obj_tag(v_e_462_) == 9)
{
lean_object* v_a_497_; 
v_a_497_ = lean_ctor_get(v_e_462_, 0);
lean_inc_ref(v_a_497_);
lean_dec_ref_known(v_e_462_, 1);
if (lean_obj_tag(v_a_497_) == 0)
{
uint8_t v___x_498_; 
lean_dec_ref_known(v_a_497_, 1);
v___x_498_ = 1;
return v___x_498_;
}
else
{
lean_dec_ref(v_a_497_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_494_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_492_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_490_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_484_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_480_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_476_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_474_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_472_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_470_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_468_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_466_;
}
}
else
{
lean_dec_ref(v_e_462_);
return v___y_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
return v_x_504_;
}
else
{
lean_object* v_key_506_; lean_object* v_value_507_; lean_object* v_tail_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_531_; 
v_key_506_ = lean_ctor_get(v_x_505_, 0);
v_value_507_ = lean_ctor_get(v_x_505_, 1);
v_tail_508_ = lean_ctor_get(v_x_505_, 2);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_531_ == 0)
{
v___x_510_ = v_x_505_;
v_isShared_511_ = v_isSharedCheck_531_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_tail_508_);
lean_inc(v_value_507_);
lean_inc(v_key_506_);
lean_dec(v_x_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_531_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v_fold_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_512_ = lean_array_get_size(v_x_504_);
v___x_513_ = l_Lean_Expr_hash(v_key_506_);
v___x_514_ = 32ULL;
v___x_515_ = lean_uint64_shift_right(v___x_513_, v___x_514_);
v_fold_516_ = lean_uint64_xor(v___x_513_, v___x_515_);
v___x_517_ = 16ULL;
v___x_518_ = lean_uint64_shift_right(v_fold_516_, v___x_517_);
v___x_519_ = lean_uint64_xor(v_fold_516_, v___x_518_);
v___x_520_ = lean_uint64_to_usize(v___x_519_);
v___x_521_ = lean_usize_of_nat(v___x_512_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_usize_land(v___x_520_, v___x_523_);
v___x_525_ = lean_array_uget_borrowed(v_x_504_, v___x_524_);
lean_inc(v___x_525_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 2, v___x_525_);
v___x_527_ = v___x_510_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_key_506_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_value_507_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v___x_525_);
v___x_527_ = v_reuseFailAlloc_530_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_array_uset(v_x_504_, v___x_524_, v___x_527_);
v_x_504_ = v___x_528_;
v_x_505_ = v_tail_508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_532_, lean_object* v_source_533_, lean_object* v_target_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_array_get_size(v_source_533_);
v___x_536_ = lean_nat_dec_lt(v_i_532_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec_ref(v_source_533_);
lean_dec(v_i_532_);
return v_target_534_;
}
else
{
lean_object* v_es_537_; lean_object* v___x_538_; lean_object* v_source_539_; lean_object* v_target_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_es_537_ = lean_array_fget(v_source_533_, v_i_532_);
v___x_538_ = lean_box(0);
v_source_539_ = lean_array_fset(v_source_533_, v_i_532_, v___x_538_);
v_target_540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_534_, v_es_537_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_i_532_, v___x_541_);
lean_dec(v_i_532_);
v_i_532_ = v___x_542_;
v_source_533_ = v_source_539_;
v_target_534_ = v_target_540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_nbuckets_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_545_ = lean_array_get_size(v_data_544_);
v___x_546_ = lean_unsigned_to_nat(2u);
v_nbuckets_547_ = lean_nat_mul(v___x_545_, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_box(0);
v___x_550_ = lean_mk_array(v_nbuckets_547_, v___x_549_);
v___x_551_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_548_, v_data_544_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_dec(v_b_553_);
lean_dec_ref(v_a_552_);
return v_x_554_;
}
else
{
lean_object* v_key_555_; lean_object* v_value_556_; lean_object* v_tail_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_569_; 
v_key_555_ = lean_ctor_get(v_x_554_, 0);
v_value_556_ = lean_ctor_get(v_x_554_, 1);
v_tail_557_ = lean_ctor_get(v_x_554_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_569_ == 0)
{
v___x_559_ = v_x_554_;
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_tail_557_);
lean_inc(v_value_556_);
lean_inc(v_key_555_);
lean_dec(v_x_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; 
v___x_561_ = lean_expr_eqv(v_key_555_, v_a_552_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_552_, v_b_553_, v_tail_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 2, v___x_562_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_key_555_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_value_556_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v___x_567_; 
lean_dec(v_value_556_);
lean_dec(v_key_555_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v_b_553_);
lean_ctor_set(v___x_559_, 0, v_a_552_);
v___x_567_ = v___x_559_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_552_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_b_553_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_tail_557_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_570_, lean_object* v_x_571_){
_start:
{
if (lean_obj_tag(v_x_571_) == 0)
{
uint8_t v___x_572_; 
v___x_572_ = 0;
return v___x_572_;
}
else
{
lean_object* v_key_573_; lean_object* v_tail_574_; uint8_t v___x_575_; 
v_key_573_ = lean_ctor_get(v_x_571_, 0);
v_tail_574_ = lean_ctor_get(v_x_571_, 2);
v___x_575_ = lean_expr_eqv(v_key_573_, v_a_570_);
if (v___x_575_ == 0)
{
v_x_571_ = v_tail_574_;
goto _start;
}
else
{
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_577_, v_x_578_);
lean_dec(v_x_578_);
lean_dec_ref(v_a_577_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_size_584_; lean_object* v_buckets_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_628_; 
v_size_584_ = lean_ctor_get(v_m_581_, 0);
v_buckets_585_ = lean_ctor_get(v_m_581_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_m_581_);
if (v_isSharedCheck_628_ == 0)
{
v___x_587_ = v_m_581_;
v_isShared_588_ = v_isSharedCheck_628_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_buckets_585_);
lean_inc(v_size_584_);
lean_dec(v_m_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_628_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v_fold_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v_bkt_602_; uint8_t v___x_603_; 
v___x_589_ = lean_array_get_size(v_buckets_585_);
v___x_590_ = l_Lean_Expr_hash(v_a_582_);
v___x_591_ = 32ULL;
v___x_592_ = lean_uint64_shift_right(v___x_590_, v___x_591_);
v_fold_593_ = lean_uint64_xor(v___x_590_, v___x_592_);
v___x_594_ = 16ULL;
v___x_595_ = lean_uint64_shift_right(v_fold_593_, v___x_594_);
v___x_596_ = lean_uint64_xor(v_fold_593_, v___x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = lean_usize_of_nat(v___x_589_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_sub(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_land(v___x_597_, v___x_600_);
v_bkt_602_ = lean_array_uget_borrowed(v_buckets_585_, v___x_601_);
v___x_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_582_, v_bkt_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v_size_x27_605_; lean_object* v___x_606_; lean_object* v_buckets_x27_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v_size_x27_605_ = lean_nat_add(v_size_584_, v___x_604_);
lean_dec(v_size_584_);
lean_inc(v_bkt_602_);
v___x_606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_606_, 0, v_a_582_);
lean_ctor_set(v___x_606_, 1, v_b_583_);
lean_ctor_set(v___x_606_, 2, v_bkt_602_);
v_buckets_x27_607_ = lean_array_uset(v_buckets_585_, v___x_601_, v___x_606_);
v___x_608_ = lean_unsigned_to_nat(4u);
v___x_609_ = lean_nat_mul(v_size_x27_605_, v___x_608_);
v___x_610_ = lean_unsigned_to_nat(3u);
v___x_611_ = lean_nat_div(v___x_609_, v___x_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_array_get_size(v_buckets_x27_607_);
v___x_613_ = lean_nat_dec_le(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
if (v___x_613_ == 0)
{
lean_object* v_val_614_; lean_object* v___x_616_; 
v_val_614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_607_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_val_614_);
lean_ctor_set(v___x_587_, 0, v_size_x27_605_);
v___x_616_ = v___x_587_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_size_x27_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_val_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
else
{
lean_object* v___x_619_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_buckets_x27_607_);
lean_ctor_set(v___x_587_, 0, v_size_x27_605_);
v___x_619_ = v___x_587_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_size_x27_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_buckets_x27_607_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v___x_621_; lean_object* v_buckets_x27_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_inc(v_bkt_602_);
v___x_621_ = lean_box(0);
v_buckets_x27_622_ = lean_array_uset(v_buckets_585_, v___x_601_, v___x_621_);
v___x_623_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_582_, v_b_583_, v_bkt_602_);
v___x_624_ = lean_array_uset(v_buckets_x27_622_, v___x_601_, v___x_623_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_624_);
v___x_626_ = v___x_587_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_size_584_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_629_, lean_object* v_as_x27_630_, lean_object* v_b_631_){
_start:
{
if (lean_obj_tag(v_as_x27_630_) == 0)
{
lean_dec_ref(v_v_629_);
return v_b_631_;
}
else
{
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_634_; 
v_head_632_ = lean_ctor_get(v_as_x27_630_, 0);
v_tail_633_ = lean_ctor_get(v_as_x27_630_, 1);
lean_inc_ref(v_v_629_);
lean_inc(v_head_632_);
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_631_, v_head_632_, v_v_629_);
v_as_x27_630_ = v_tail_633_;
v_b_631_ = v___x_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_636_, lean_object* v_as_x27_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_636_, v_as_x27_637_, v_b_638_);
lean_dec(v_as_x27_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_640_, lean_object* v_e_641_, lean_object* v_v_642_, lean_object* v_a_643_){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = 0;
v___x_645_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_640_, v_e_641_, v___x_644_);
v___x_646_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_642_, v___x_645_, v_a_643_);
lean_dec(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_647_, lean_object* v_e_648_, lean_object* v_v_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_647_, v_e_648_, v_v_649_, v_a_650_);
lean_dec_ref(v_goal_647_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_652_, lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_653_, v_a_654_, v_b_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_657_, lean_object* v_as_658_, lean_object* v_as_x27_659_, lean_object* v_b_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_657_, v_as_x27_659_, v_b_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_663_, lean_object* v_as_664_, lean_object* v_as_x27_665_, lean_object* v_b_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_663_, v_as_664_, v_as_x27_665_, v_b_666_, v_a_667_);
lean_dec(v_as_x27_665_);
lean_dec(v_as_664_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_673_, lean_object* v_a_674_, lean_object* v_x_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_673_, v_a_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_a_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_678_, lean_object* v_data_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_681_, lean_object* v_a_682_, lean_object* v_b_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_682_, v_b_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_686_, lean_object* v_i_687_, lean_object* v_source_688_, lean_object* v_target_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_687_, v_source_688_, v_target_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_692_, v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
return v_x_695_;
}
else
{
lean_object* v_key_697_; lean_object* v_value_698_; lean_object* v_tail_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_736_; 
v_key_697_ = lean_ctor_get(v_x_696_, 0);
v_value_698_ = lean_ctor_get(v_x_696_, 1);
v_tail_699_ = lean_ctor_get(v_x_696_, 2);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_736_ == 0)
{
v___x_701_ = v_x_696_;
v_isShared_702_ = v_isSharedCheck_736_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_tail_699_);
lean_inc(v_value_698_);
lean_inc(v_key_697_);
lean_dec(v_x_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_736_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint64_t v___y_705_; lean_object* v_intZero_723_; uint8_t v_isNeg_724_; 
v___x_703_ = lean_array_get_size(v_x_695_);
v_intZero_723_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_724_ = lean_int_dec_lt(v_key_697_, v_intZero_723_);
if (v_isNeg_724_ == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint64_t v___x_728_; 
v_a_725_ = lean_nat_abs(v_key_697_);
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_nat_mul(v___x_726_, v_a_725_);
lean_dec(v_a_725_);
v___x_728_ = lean_uint64_of_nat(v___x_727_);
lean_dec(v___x_727_);
v___y_705_ = v___x_728_;
goto v___jp_704_;
}
else
{
lean_object* v_abs_729_; lean_object* v_one_730_; lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint64_t v___x_735_; 
v_abs_729_ = lean_nat_abs(v_key_697_);
v_one_730_ = lean_unsigned_to_nat(1u);
v_a_731_ = lean_nat_sub(v_abs_729_, v_one_730_);
lean_dec(v_abs_729_);
v___x_732_ = lean_unsigned_to_nat(2u);
v___x_733_ = lean_nat_mul(v___x_732_, v_a_731_);
lean_dec(v_a_731_);
v___x_734_ = lean_nat_add(v___x_733_, v_one_730_);
lean_dec(v___x_733_);
v___x_735_ = lean_uint64_of_nat(v___x_734_);
lean_dec(v___x_734_);
v___y_705_ = v___x_735_;
goto v___jp_704_;
}
v___jp_704_:
{
uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v_fold_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_706_ = 32ULL;
v___x_707_ = lean_uint64_shift_right(v___y_705_, v___x_706_);
v_fold_708_ = lean_uint64_xor(v___y_705_, v___x_707_);
v___x_709_ = 16ULL;
v___x_710_ = lean_uint64_shift_right(v_fold_708_, v___x_709_);
v___x_711_ = lean_uint64_xor(v_fold_708_, v___x_710_);
v___x_712_ = lean_uint64_to_usize(v___x_711_);
v___x_713_ = lean_usize_of_nat(v___x_703_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_sub(v___x_713_, v___x_714_);
v___x_716_ = lean_usize_land(v___x_712_, v___x_715_);
v___x_717_ = lean_array_uget_borrowed(v_x_695_, v___x_716_);
lean_inc(v___x_717_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 2, v___x_717_);
v___x_719_ = v___x_701_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_key_697_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_value_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_717_);
v___x_719_ = v_reuseFailAlloc_722_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_array_uset(v_x_695_, v___x_716_, v___x_719_);
v_x_695_ = v___x_720_;
v_x_696_ = v_tail_699_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_737_, lean_object* v_source_738_, lean_object* v_target_739_){
_start:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_array_get_size(v_source_738_);
v___x_741_ = lean_nat_dec_lt(v_i_737_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec_ref(v_source_738_);
lean_dec(v_i_737_);
return v_target_739_;
}
else
{
lean_object* v_es_742_; lean_object* v___x_743_; lean_object* v_source_744_; lean_object* v_target_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_es_742_ = lean_array_fget(v_source_738_, v_i_737_);
v___x_743_ = lean_box(0);
v_source_744_ = lean_array_fset(v_source_738_, v_i_737_, v___x_743_);
v_target_745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_739_, v_es_742_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_i_737_, v___x_746_);
lean_dec(v_i_737_);
v_i_737_ = v___x_747_;
v_source_738_ = v_source_744_;
v_target_739_ = v_target_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_nbuckets_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_750_ = lean_array_get_size(v_data_749_);
v___x_751_ = lean_unsigned_to_nat(2u);
v_nbuckets_752_ = lean_nat_mul(v___x_750_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_box(0);
v___x_755_ = lean_mk_array(v_nbuckets_752_, v___x_754_);
v___x_756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_753_, v_data_749_, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_757_, lean_object* v_a_758_, lean_object* v_b_759_){
_start:
{
lean_object* v_size_760_; lean_object* v_buckets_761_; lean_object* v___x_762_; uint64_t v___y_764_; lean_object* v_intZero_801_; uint8_t v_isNeg_802_; 
v_size_760_ = lean_ctor_get(v_m_757_, 0);
v_buckets_761_ = lean_ctor_get(v_m_757_, 1);
v___x_762_ = lean_array_get_size(v_buckets_761_);
v_intZero_801_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_802_ = lean_int_dec_lt(v_a_758_, v_intZero_801_);
if (v_isNeg_802_ == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint64_t v___x_806_; 
v_a_803_ = lean_nat_abs(v_a_758_);
v___x_804_ = lean_unsigned_to_nat(2u);
v___x_805_ = lean_nat_mul(v___x_804_, v_a_803_);
lean_dec(v_a_803_);
v___x_806_ = lean_uint64_of_nat(v___x_805_);
lean_dec(v___x_805_);
v___y_764_ = v___x_806_;
goto v___jp_763_;
}
else
{
lean_object* v_abs_807_; lean_object* v_one_808_; lean_object* v_a_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint64_t v___x_813_; 
v_abs_807_ = lean_nat_abs(v_a_758_);
v_one_808_ = lean_unsigned_to_nat(1u);
v_a_809_ = lean_nat_sub(v_abs_807_, v_one_808_);
lean_dec(v_abs_807_);
v___x_810_ = lean_unsigned_to_nat(2u);
v___x_811_ = lean_nat_mul(v___x_810_, v_a_809_);
lean_dec(v_a_809_);
v___x_812_ = lean_nat_add(v___x_811_, v_one_808_);
lean_dec(v___x_811_);
v___x_813_ = lean_uint64_of_nat(v___x_812_);
lean_dec(v___x_812_);
v___y_764_ = v___x_813_;
goto v___jp_763_;
}
v___jp_763_:
{
uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v_fold_767_; uint64_t v___x_768_; uint64_t v___x_769_; uint64_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_bkt_776_; uint8_t v___x_777_; 
v___x_765_ = 32ULL;
v___x_766_ = lean_uint64_shift_right(v___y_764_, v___x_765_);
v_fold_767_ = lean_uint64_xor(v___y_764_, v___x_766_);
v___x_768_ = 16ULL;
v___x_769_ = lean_uint64_shift_right(v_fold_767_, v___x_768_);
v___x_770_ = lean_uint64_xor(v_fold_767_, v___x_769_);
v___x_771_ = lean_uint64_to_usize(v___x_770_);
v___x_772_ = lean_usize_of_nat(v___x_762_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_sub(v___x_772_, v___x_773_);
v___x_775_ = lean_usize_land(v___x_771_, v___x_774_);
v_bkt_776_ = lean_array_uget_borrowed(v_buckets_761_, v___x_775_);
v___x_777_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_758_, v_bkt_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_798_; 
lean_inc_ref(v_buckets_761_);
lean_inc(v_size_760_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_m_757_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; 
v_unused_799_ = lean_ctor_get(v_m_757_, 1);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_m_757_, 0);
lean_dec(v_unused_800_);
v___x_779_ = v_m_757_;
v_isShared_780_ = v_isSharedCheck_798_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_m_757_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_798_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_size_x27_782_; lean_object* v___x_783_; lean_object* v_buckets_x27_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v_size_x27_782_ = lean_nat_add(v_size_760_, v___x_781_);
lean_dec(v_size_760_);
lean_inc(v_bkt_776_);
v___x_783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_783_, 0, v_a_758_);
lean_ctor_set(v___x_783_, 1, v_b_759_);
lean_ctor_set(v___x_783_, 2, v_bkt_776_);
v_buckets_x27_784_ = lean_array_uset(v_buckets_761_, v___x_775_, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(4u);
v___x_786_ = lean_nat_mul(v_size_x27_782_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(3u);
v___x_788_ = lean_nat_div(v___x_786_, v___x_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_array_get_size(v_buckets_x27_784_);
v___x_790_ = lean_nat_dec_le(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v_val_791_; lean_object* v___x_793_; 
v_val_791_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_784_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_val_791_);
lean_ctor_set(v___x_779_, 0, v_size_x27_782_);
v___x_793_ = v___x_779_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_size_x27_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_val_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
else
{
lean_object* v___x_796_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_buckets_x27_784_);
lean_ctor_set(v___x_779_, 0, v_size_x27_782_);
v___x_796_ = v___x_779_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_size_x27_782_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_buckets_x27_784_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_dec(v_b_759_);
lean_dec(v_a_758_);
return v_m_757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_814_, lean_object* v_isTarget_815_, lean_object* v_as_816_, size_t v_sz_817_, size_t v_i_818_, lean_object* v_b_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = lean_usize_dec_lt(v_i_818_, v_sz_817_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_isTarget_815_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_b_819_);
return v___x_826_;
}
else
{
lean_object* v_snd_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_909_; 
v_snd_827_ = lean_ctor_get(v_b_819_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_b_819_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_b_819_, 0);
lean_dec(v_unused_910_);
v___x_829_ = v_b_819_;
v_isShared_830_ = v_isSharedCheck_909_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snd_827_);
lean_dec(v_b_819_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_909_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_array_uget_borrowed(v_as_816_, v_i_818_);
lean_inc(v_a_831_);
v___x_832_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_814_, v_a_831_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_snd_833_; lean_object* v_a_834_; lean_object* v_fst_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_899_; 
v_snd_833_ = lean_ctor_get(v_snd_827_, 1);
lean_inc(v_snd_833_);
v_a_834_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_832_, 1);
v_fst_835_ = lean_ctor_get(v_snd_827_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_snd_827_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_snd_827_, 1);
lean_dec(v_unused_900_);
v___x_837_ = v_snd_827_;
v_isShared_838_ = v_isSharedCheck_899_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_fst_835_);
lean_dec(v_snd_827_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_899_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_898_; 
v_fst_839_ = lean_ctor_get(v_snd_833_, 0);
v_snd_840_ = lean_ctor_get(v_snd_833_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_snd_833_);
if (v_isSharedCheck_898_ == 0)
{
v___x_842_ = v_snd_833_;
v_isShared_843_ = v_isSharedCheck_898_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
lean_dec(v_snd_833_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_898_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v_a_846_; uint8_t v___x_853_; 
v___x_844_ = lean_box(0);
v___x_853_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_834_);
if (v___x_853_ == 0)
{
lean_object* v___x_855_; 
lean_dec(v_a_834_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_snd_840_);
lean_ctor_set(v___x_837_, 0, v_fst_839_);
v___x_855_ = v___x_837_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_839_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_840_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_855_);
lean_ctor_set(v___x_829_, 0, v_fst_835_);
v___x_857_ = v___x_829_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
v_a_846_ = v___x_857_;
goto v___jp_845_;
}
}
}
else
{
lean_object* v___x_860_; 
lean_inc_ref(v_isTarget_815_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v___y_821_);
lean_inc_ref(v___y_820_);
lean_inc(v_a_834_);
v___x_860_ = lean_apply_6(v_isTarget_815_, v_a_834_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, lean_box(0));
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; uint8_t v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_864_; 
lean_dec(v_a_834_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_snd_840_);
lean_ctor_set(v___x_837_, 0, v_fst_839_);
v___x_864_ = v___x_837_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fst_839_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_snd_840_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_864_);
lean_ctor_set(v___x_829_, 0, v_fst_835_);
v___x_866_ = v___x_829_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
v_a_846_ = v___x_866_;
goto v___jp_845_;
}
}
}
else
{
lean_object* v_self_869_; lean_object* v___x_870_; 
v_self_869_ = lean_ctor_get(v_a_834_, 0);
lean_inc_ref(v_self_869_);
lean_dec(v_a_834_);
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_840_, v_self_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_814_, v_snd_840_, v_self_869_, v_fst_839_, v_fst_835_);
lean_inc_n(v___x_871_, 2);
v___x_872_ = l_Rat_ofInt(v___x_871_);
v___x_873_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_814_, v_self_869_, v___x_872_, v_snd_840_);
v___x_874_ = lean_box(0);
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_839_, v___x_871_, v___x_874_);
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_877_ = lean_int_add(v___x_871_, v___x_876_);
lean_dec(v___x_871_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_873_);
lean_ctor_set(v___x_837_, 0, v___x_875_);
v___x_879_ = v___x_837_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_873_);
v___x_879_ = v_reuseFailAlloc_883_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_879_);
lean_ctor_set(v___x_829_, 0, v___x_877_);
v___x_881_ = v___x_829_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
v_a_846_ = v___x_881_;
goto v___jp_845_;
}
}
}
else
{
lean_object* v___x_885_; 
lean_dec_ref_known(v___x_870_, 1);
lean_dec_ref(v_self_869_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_snd_840_);
lean_ctor_set(v___x_837_, 0, v_fst_839_);
v___x_885_ = v___x_837_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_839_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_840_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___x_885_);
lean_ctor_set(v___x_829_, 0, v_fst_835_);
v___x_887_ = v___x_829_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_835_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
v_a_846_ = v___x_887_;
goto v___jp_845_;
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_842_);
lean_dec(v_snd_840_);
lean_dec(v_fst_839_);
lean_del_object(v___x_837_);
lean_dec(v_fst_835_);
lean_dec(v_a_834_);
lean_del_object(v___x_829_);
lean_dec_ref(v_isTarget_815_);
v_a_890_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_860_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_860_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
v___jp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_a_846_);
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_a_846_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
size_t v___x_849_; size_t v___x_850_; 
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_818_, v___x_849_);
v_i_818_ = v___x_850_;
v_b_819_ = v___x_848_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_829_);
lean_dec(v_snd_827_);
lean_dec_ref(v_isTarget_815_);
v_a_901_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_832_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_832_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_911_, lean_object* v_isTarget_912_, lean_object* v_as_913_, lean_object* v_sz_914_, lean_object* v_i_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
size_t v_sz_boxed_922_; size_t v_i_boxed_923_; lean_object* v_res_924_; 
v_sz_boxed_922_ = lean_unbox_usize(v_sz_914_);
lean_dec(v_sz_914_);
v_i_boxed_923_ = lean_unbox_usize(v_i_915_);
lean_dec(v_i_915_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_911_, v_isTarget_912_, v_as_913_, v_sz_boxed_922_, v_i_boxed_923_, v_b_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_as_913_);
lean_dec_ref(v_goal_911_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_925_, lean_object* v_isTarget_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
lean_dec_ref(v_isTarget_926_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_930_);
return v___x_937_;
}
else
{
lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1020_; 
v_snd_938_ = lean_ctor_get(v_b_930_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_b_930_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_b_930_, 0);
lean_dec(v_unused_1021_);
v___x_940_ = v_b_930_;
v_isShared_941_ = v_isSharedCheck_1020_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_dec(v_b_930_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1020_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_a_942_; lean_object* v___x_943_; 
v_a_942_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
lean_inc(v_a_942_);
v___x_943_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_925_, v_a_942_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_snd_944_; lean_object* v_a_945_; lean_object* v_fst_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1010_; 
v_snd_944_ = lean_ctor_get(v_snd_938_, 1);
lean_inc(v_snd_944_);
v_a_945_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_943_, 1);
v_fst_946_ = lean_ctor_get(v_snd_938_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_snd_938_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_snd_938_, 1);
lean_dec(v_unused_1011_);
v___x_948_ = v_snd_938_;
v_isShared_949_ = v_isSharedCheck_1010_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_fst_946_);
lean_dec(v_snd_938_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1010_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1009_; 
v_fst_950_ = lean_ctor_get(v_snd_944_, 0);
v_snd_951_ = lean_ctor_get(v_snd_944_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_snd_944_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_953_ = v_snd_944_;
v_isShared_954_ = v_isSharedCheck_1009_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_inc(v_fst_950_);
lean_dec(v_snd_944_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1009_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_a_957_; uint8_t v___x_964_; 
v___x_955_ = lean_box(0);
v___x_964_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_945_);
if (v___x_964_ == 0)
{
lean_object* v___x_966_; 
lean_dec(v_a_945_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_966_ = v___x_948_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_snd_951_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_966_);
lean_ctor_set(v___x_940_, 0, v_fst_946_);
v___x_968_ = v___x_940_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_a_957_ = v___x_968_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_971_; 
lean_inc_ref(v_isTarget_926_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v_a_945_);
v___x_971_ = lean_apply_6(v_isTarget_926_, v_a_945_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, lean_box(0));
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; uint8_t v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = lean_unbox(v_a_972_);
lean_dec(v_a_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v_a_945_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_975_ = v___x_948_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_snd_951_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_975_);
lean_ctor_set(v___x_940_, 0, v_fst_946_);
v___x_977_ = v___x_940_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
v_a_957_ = v___x_977_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v_self_980_; lean_object* v___x_981_; 
v_self_980_ = lean_ctor_get(v_a_945_, 0);
lean_inc_ref(v_self_980_);
lean_dec(v_a_945_);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_951_, v_self_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_982_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_925_, v_snd_951_, v_self_980_, v_fst_950_, v_fst_946_);
lean_inc_n(v___x_982_, 2);
v___x_983_ = l_Rat_ofInt(v___x_982_);
v___x_984_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_925_, v_self_980_, v___x_983_, v_snd_951_);
v___x_985_ = lean_box(0);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_950_, v___x_982_, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_988_ = lean_int_add(v___x_982_, v___x_987_);
lean_dec(v___x_982_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_984_);
lean_ctor_set(v___x_948_, 0, v___x_986_);
v___x_990_ = v___x_948_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_984_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_990_);
lean_ctor_set(v___x_940_, 0, v___x_988_);
v___x_992_ = v___x_940_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
v_a_957_ = v___x_992_;
goto v___jp_956_;
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec_ref_known(v___x_981_, 1);
lean_dec_ref(v_self_980_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_snd_951_);
lean_ctor_set(v___x_948_, 0, v_fst_950_);
v___x_996_ = v___x_948_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_fst_950_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_snd_951_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_996_);
lean_ctor_set(v___x_940_, 0, v_fst_946_);
v___x_998_ = v___x_940_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_fst_946_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v_a_957_ = v___x_998_;
goto v___jp_956_;
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_953_);
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
lean_del_object(v___x_948_);
lean_dec(v_fst_946_);
lean_dec(v_a_945_);
lean_del_object(v___x_940_);
lean_dec_ref(v_isTarget_926_);
v_a_1001_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_971_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_971_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
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
v___x_961_ = lean_usize_add(v_i_929_, v___x_960_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_925_, v_isTarget_926_, v_as_927_, v_sz_928_, v___x_961_, v___x_959_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_962_;
}
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_940_);
lean_dec(v_snd_938_);
lean_dec_ref(v_isTarget_926_);
v_a_1012_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_943_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_943_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1022_, lean_object* v_isTarget_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1022_, v_isTarget_1023_, v_as_1024_, v_sz_boxed_1033_, v_i_boxed_1034_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
lean_dec_ref(v_goal_1022_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1036_, lean_object* v_isTarget_1037_, lean_object* v_as_1038_, size_t v_sz_1039_, size_t v_i_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_lt(v_i_1040_, v_sz_1039_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v_isTarget_1037_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_b_1041_);
return v___x_1048_;
}
else
{
lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1131_; 
v_snd_1049_ = lean_ctor_get(v_b_1041_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_b_1041_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v_b_1041_, 0);
lean_dec(v_unused_1132_);
v___x_1051_ = v_b_1041_;
v_isShared_1052_ = v_isSharedCheck_1131_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_dec(v_b_1041_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1131_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_array_uget_borrowed(v_as_1038_, v_i_1040_);
lean_inc(v_a_1053_);
v___x_1054_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1036_, v_a_1053_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_snd_1055_; lean_object* v_a_1056_; lean_object* v_fst_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1121_; 
v_snd_1055_ = lean_ctor_get(v_snd_1049_, 1);
lean_inc(v_snd_1055_);
v_a_1056_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1054_, 1);
v_fst_1057_ = lean_ctor_get(v_snd_1049_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_snd_1049_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_snd_1049_, 1);
lean_dec(v_unused_1122_);
v___x_1059_ = v_snd_1049_;
v_isShared_1060_ = v_isSharedCheck_1121_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_fst_1057_);
lean_dec(v_snd_1049_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1121_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1120_; 
v_fst_1061_ = lean_ctor_get(v_snd_1055_, 0);
v_snd_1062_ = lean_ctor_get(v_snd_1055_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_snd_1055_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1064_ = v_snd_1055_;
v_isShared_1065_ = v_isSharedCheck_1120_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_snd_1062_);
lean_inc(v_fst_1061_);
lean_dec(v_snd_1055_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1120_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v_a_1068_; uint8_t v___x_1075_; 
v___x_1066_ = lean_box(0);
v___x_1075_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1056_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1077_; 
lean_dec(v_a_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v_snd_1062_);
lean_ctor_set(v___x_1059_, 0, v_fst_1061_);
v___x_1077_ = v___x_1059_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_snd_1062_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1079_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1077_);
lean_ctor_set(v___x_1051_, 0, v_fst_1057_);
v___x_1079_ = v___x_1051_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fst_1057_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
v_a_1068_ = v___x_1079_;
goto v___jp_1067_;
}
}
}
else
{
lean_object* v___x_1082_; 
lean_inc_ref(v_isTarget_1037_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v_a_1056_);
v___x_1082_ = lean_apply_6(v_isTarget_1037_, v_a_1056_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, lean_box(0));
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; uint8_t v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = lean_unbox(v_a_1083_);
lean_dec(v_a_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_a_1056_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v_snd_1062_);
lean_ctor_set(v___x_1059_, 0, v_fst_1061_);
v___x_1086_ = v___x_1059_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1062_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1086_);
lean_ctor_set(v___x_1051_, 0, v_fst_1057_);
v___x_1088_ = v___x_1051_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_fst_1057_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v_a_1068_ = v___x_1088_;
goto v___jp_1067_;
}
}
}
else
{
lean_object* v_self_1091_; lean_object* v___x_1092_; 
v_self_1091_ = lean_ctor_get(v_a_1056_, 0);
lean_inc_ref(v_self_1091_);
lean_dec(v_a_1056_);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1062_, v_self_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1093_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1036_, v_snd_1062_, v_self_1091_, v_fst_1061_, v_fst_1057_);
lean_inc_n(v___x_1093_, 2);
v___x_1094_ = l_Rat_ofInt(v___x_1093_);
v___x_1095_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1036_, v_self_1091_, v___x_1094_, v_snd_1062_);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1061_, v___x_1093_, v___x_1096_);
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1099_ = lean_int_add(v___x_1093_, v___x_1098_);
lean_dec(v___x_1093_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1095_);
lean_ctor_set(v___x_1059_, 0, v___x_1097_);
v___x_1101_ = v___x_1059_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1095_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1101_);
lean_ctor_set(v___x_1051_, 0, v___x_1099_);
v___x_1103_ = v___x_1051_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v_a_1068_ = v___x_1103_;
goto v___jp_1067_;
}
}
}
else
{
lean_object* v___x_1107_; 
lean_dec_ref_known(v___x_1092_, 1);
lean_dec_ref(v_self_1091_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v_snd_1062_);
lean_ctor_set(v___x_1059_, 0, v_fst_1061_);
v___x_1107_ = v___x_1059_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1061_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_snd_1062_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1107_);
lean_ctor_set(v___x_1051_, 0, v_fst_1057_);
v___x_1109_ = v___x_1051_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1057_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v_a_1068_ = v___x_1109_;
goto v___jp_1067_;
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_1064_);
lean_dec(v_snd_1062_);
lean_dec(v_fst_1061_);
lean_del_object(v___x_1059_);
lean_dec(v_fst_1057_);
lean_dec(v_a_1056_);
lean_del_object(v___x_1051_);
lean_dec_ref(v_isTarget_1037_);
v_a_1112_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1082_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1082_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
v___jp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_a_1068_);
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1070_ = v___x_1064_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_a_1068_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
size_t v___x_1071_; size_t v___x_1072_; 
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_add(v_i_1040_, v___x_1071_);
v_i_1040_ = v___x_1072_;
v_b_1041_ = v___x_1070_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_del_object(v___x_1051_);
lean_dec(v_snd_1049_);
lean_dec_ref(v_isTarget_1037_);
v_a_1123_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1054_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1054_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1133_, lean_object* v_isTarget_1134_, lean_object* v_as_1135_, lean_object* v_sz_1136_, lean_object* v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1136_);
lean_dec(v_sz_1136_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1137_);
lean_dec(v_i_1137_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1133_, v_isTarget_1134_, v_as_1135_, v_sz_boxed_1144_, v_i_boxed_1145_, v_b_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec_ref(v_as_1135_);
lean_dec_ref(v_goal_1133_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1147_, lean_object* v_isTarget_1148_, lean_object* v_as_1149_, size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_b_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_isTarget_1148_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_b_1152_);
return v___x_1159_;
}
else
{
lean_object* v_snd_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1242_; 
v_snd_1160_ = lean_ctor_get(v_b_1152_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_b_1152_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_b_1152_, 0);
lean_dec(v_unused_1243_);
v___x_1162_ = v_b_1152_;
v_isShared_1163_ = v_isSharedCheck_1242_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snd_1160_);
lean_dec(v_b_1152_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1242_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_a_1164_; lean_object* v___x_1165_; 
v_a_1164_ = lean_array_uget_borrowed(v_as_1149_, v_i_1151_);
lean_inc(v_a_1164_);
v___x_1165_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1147_, v_a_1164_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_snd_1166_; lean_object* v_a_1167_; lean_object* v_fst_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1232_; 
v_snd_1166_ = lean_ctor_get(v_snd_1160_, 1);
lean_inc(v_snd_1166_);
v_a_1167_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1165_, 1);
v_fst_1168_ = lean_ctor_get(v_snd_1160_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_snd_1160_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_snd_1160_, 1);
lean_dec(v_unused_1233_);
v___x_1170_ = v_snd_1160_;
v_isShared_1171_ = v_isSharedCheck_1232_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_fst_1168_);
lean_dec(v_snd_1160_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1232_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1231_; 
v_fst_1172_ = lean_ctor_get(v_snd_1166_, 0);
v_snd_1173_ = lean_ctor_get(v_snd_1166_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_snd_1166_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1175_ = v_snd_1166_;
v_isShared_1176_ = v_isSharedCheck_1231_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_snd_1173_);
lean_inc(v_fst_1172_);
lean_dec(v_snd_1166_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1231_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v_a_1179_; uint8_t v___x_1186_; 
v___x_1177_ = lean_box(0);
v___x_1186_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1167_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1188_; 
lean_dec(v_a_1167_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_snd_1173_);
lean_ctor_set(v___x_1170_, 0, v_fst_1172_);
v___x_1188_ = v___x_1170_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1172_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_snd_1173_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1188_);
lean_ctor_set(v___x_1162_, 0, v_fst_1168_);
v___x_1190_ = v___x_1162_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1168_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_a_1179_ = v___x_1190_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1193_; 
lean_inc_ref(v_isTarget_1148_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v_a_1167_);
v___x_1193_ = lean_apply_6(v_isTarget_1148_, v_a_1167_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, lean_box(0));
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; uint8_t v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = lean_unbox(v_a_1194_);
lean_dec(v_a_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1197_; 
lean_dec(v_a_1167_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_snd_1173_);
lean_ctor_set(v___x_1170_, 0, v_fst_1172_);
v___x_1197_ = v___x_1170_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_fst_1172_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_snd_1173_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1197_);
lean_ctor_set(v___x_1162_, 0, v_fst_1168_);
v___x_1199_ = v___x_1162_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_fst_1168_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v_a_1179_ = v___x_1199_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v_self_1202_; lean_object* v___x_1203_; 
v_self_1202_ = lean_ctor_get(v_a_1167_, 0);
lean_inc_ref(v_self_1202_);
lean_dec(v_a_1167_);
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1173_, v_self_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1204_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1147_, v_snd_1173_, v_self_1202_, v_fst_1172_, v_fst_1168_);
lean_inc_n(v___x_1204_, 2);
v___x_1205_ = l_Rat_ofInt(v___x_1204_);
v___x_1206_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1147_, v_self_1202_, v___x_1205_, v_snd_1173_);
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1172_, v___x_1204_, v___x_1207_);
v___x_1209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1210_ = lean_int_add(v___x_1204_, v___x_1209_);
lean_dec(v___x_1204_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1206_);
lean_ctor_set(v___x_1170_, 0, v___x_1208_);
v___x_1212_ = v___x_1170_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1206_);
v___x_1212_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1212_);
lean_ctor_set(v___x_1162_, 0, v___x_1210_);
v___x_1214_ = v___x_1162_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v_a_1179_ = v___x_1214_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1218_; 
lean_dec_ref_known(v___x_1203_, 1);
lean_dec_ref(v_self_1202_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_snd_1173_);
lean_ctor_set(v___x_1170_, 0, v_fst_1172_);
v___x_1218_ = v___x_1170_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_fst_1172_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_snd_1173_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1218_);
lean_ctor_set(v___x_1162_, 0, v_fst_1168_);
v___x_1220_ = v___x_1162_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_fst_1168_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v_a_1179_ = v___x_1220_;
goto v___jp_1178_;
}
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_del_object(v___x_1175_);
lean_dec(v_snd_1173_);
lean_dec(v_fst_1172_);
lean_del_object(v___x_1170_);
lean_dec(v_fst_1168_);
lean_dec(v_a_1167_);
lean_del_object(v___x_1162_);
lean_dec_ref(v_isTarget_1148_);
v_a_1223_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1193_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1193_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
v___jp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_a_1179_);
lean_ctor_set(v___x_1175_, 0, v___x_1177_);
v___x_1181_ = v___x_1175_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_a_1179_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1151_, v___x_1182_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1147_, v_isTarget_1148_, v_as_1149_, v_sz_1150_, v___x_1183_, v___x_1181_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_del_object(v___x_1162_);
lean_dec(v_snd_1160_);
lean_dec_ref(v_isTarget_1148_);
v_a_1234_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1165_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1165_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
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
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_array_uget_borrowed(v_as_1329_, v_i_1331_);
lean_inc(v_snd_1340_);
lean_inc_ref(v_isTarget_1328_);
v___x_1345_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1326_, v_goal_1327_, v_isTarget_1328_, v_a_1344_, v_snd_1340_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1365_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1365_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1365_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1346_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec_ref(v_isTarget_1328_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1346_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1350_);
v___x_1352_ = v___x_1342_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1340_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_del_object(v___x_1348_);
lean_dec(v_snd_1340_);
v_a_1357_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v_a_1346_, 1);
v___x_1358_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_a_1357_);
lean_ctor_set(v___x_1342_, 0, v___x_1358_);
v___x_1360_ = v___x_1342_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1357_);
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
v_a_1366_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1345_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1345_);
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
lean_object* v_buckets_1548_; lean_object* v_used_1549_; size_t v_sz_1550_; size_t v___x_1551_; lean_object* v___x_1552_; 
v_buckets_1548_ = lean_ctor_get(v_model_1542_, 1);
v_used_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1550_ = lean_array_size(v_buckets_1548_);
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1548_, v_sz_1550_, v___x_1551_, v_used_1549_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_toGoalState_1553_; lean_object* v_a_1554_; lean_object* v_exprs_1555_; lean_object* v_nextVal_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_toGoalState_1553_ = lean_ctor_get(v_goal_1540_, 0);
v_a_1554_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1552_, 1);
v_exprs_1555_ = lean_ctor_get(v_toGoalState_1553_, 2);
v_nextVal_1556_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_a_1554_);
lean_ctor_set(v___x_1557_, 1, v_model_1542_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_nextVal_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1540_, v_isTarget_1541_, v_exprs_1555_, v___x_1558_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
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
v_a_1578_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1552_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1552_);
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
lean_object* v___x_1907_; lean_object* v_env_1908_; lean_object* v___x_1909_; lean_object* v_mctx_1910_; lean_object* v_lctx_1911_; lean_object* v_options_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1907_ = lean_st_ref_get(v___y_1905_);
v_env_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc_ref(v_env_1908_);
lean_dec(v___x_1907_);
v___x_1909_ = lean_st_ref_get(v___y_1903_);
v_mctx_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_mctx_1910_);
lean_dec(v___x_1909_);
v_lctx_1911_ = lean_ctor_get(v___y_1902_, 2);
v_options_1912_ = lean_ctor_get(v___y_1904_, 2);
lean_inc_ref(v_options_1912_);
lean_inc_ref(v_lctx_1911_);
v___x_1913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1913_, 0, v_env_1908_);
lean_ctor_set(v___x_1913_, 1, v_mctx_1910_);
lean_ctor_set(v___x_1913_, 2, v_lctx_1911_);
lean_ctor_set(v___x_1913_, 3, v_options_1912_);
v___x_1914_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_msgData_1901_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1923_; double v___x_1924_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_float_of_nat(v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_ref_1935_; lean_object* v___x_1936_; lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1981_; 
v_ref_1935_ = lean_ctor_get(v___y_1932_, 5);
v___x_1936_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1981_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1981_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v_traceState_1942_; lean_object* v_env_1943_; lean_object* v_nextMacroScope_1944_; lean_object* v_ngen_1945_; lean_object* v_auxDeclNGen_1946_; lean_object* v_cache_1947_; lean_object* v_messages_1948_; lean_object* v_infoState_1949_; lean_object* v_snapshotTasks_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1980_; 
v___x_1941_ = lean_st_ref_take(v___y_1933_);
v_traceState_1942_ = lean_ctor_get(v___x_1941_, 4);
v_env_1943_ = lean_ctor_get(v___x_1941_, 0);
v_nextMacroScope_1944_ = lean_ctor_get(v___x_1941_, 1);
v_ngen_1945_ = lean_ctor_get(v___x_1941_, 2);
v_auxDeclNGen_1946_ = lean_ctor_get(v___x_1941_, 3);
v_cache_1947_ = lean_ctor_get(v___x_1941_, 5);
v_messages_1948_ = lean_ctor_get(v___x_1941_, 6);
v_infoState_1949_ = lean_ctor_get(v___x_1941_, 7);
v_snapshotTasks_1950_ = lean_ctor_get(v___x_1941_, 8);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1952_ = v___x_1941_;
v_isShared_1953_ = v_isSharedCheck_1980_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snapshotTasks_1950_);
lean_inc(v_infoState_1949_);
lean_inc(v_messages_1948_);
lean_inc(v_cache_1947_);
lean_inc(v_traceState_1942_);
lean_inc(v_auxDeclNGen_1946_);
lean_inc(v_ngen_1945_);
lean_inc(v_nextMacroScope_1944_);
lean_inc(v_env_1943_);
lean_dec(v___x_1941_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1980_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
uint64_t v_tid_1954_; lean_object* v_traces_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1979_; 
v_tid_1954_ = lean_ctor_get_uint64(v_traceState_1942_, sizeof(void*)*1);
v_traces_1955_ = lean_ctor_get(v_traceState_1942_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_traceState_1942_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1957_ = v_traceState_1942_;
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_traces_1955_);
lean_dec(v_traceState_1942_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; double v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1961_ = 0;
v___x_1962_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1963_, 0, v_cls_1928_);
lean_ctor_set(v___x_1963_, 1, v___x_1959_);
lean_ctor_set(v___x_1963_, 2, v___x_1962_);
lean_ctor_set_float(v___x_1963_, sizeof(void*)*3, v___x_1960_);
lean_ctor_set_float(v___x_1963_, sizeof(void*)*3 + 8, v___x_1960_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*3 + 16, v___x_1961_);
v___x_1964_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v_a_1937_);
lean_ctor_set(v___x_1965_, 2, v___x_1964_);
lean_inc(v_ref_1935_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_ref_1935_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_PersistentArray_push___redArg(v_traces_1955_, v___x_1966_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1967_);
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1967_);
lean_ctor_set_uint64(v_reuseFailAlloc_1978_, sizeof(void*)*1, v_tid_1954_);
v___x_1969_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_1969_);
v___x_1971_ = v___x_1952_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_env_1943_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_nextMacroScope_1944_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_ngen_1945_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_auxDeclNGen_1946_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_cache_1947_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_messages_1948_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_infoState_1949_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_snapshotTasks_1950_);
v___x_1971_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = lean_st_ref_set(v___y_1933_, v___x_1971_);
v___x_1973_ = lean_box(0);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1973_);
v___x_1975_ = v___x_1939_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1982_, lean_object* v_msg_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1982_, v_msg_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_1994_, lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec(v_traceClass_1994_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_b_1998_);
return v___x_2005_;
}
else
{
lean_object* v_a_2006_; lean_object* v_snd_2007_; lean_object* v_fst_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2043_; 
v_a_2006_ = lean_array_uget(v_as_1995_, v_i_1997_);
v_snd_2007_ = lean_ctor_get(v_a_2006_, 1);
v_fst_2008_ = lean_ctor_get(v_a_2006_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2010_ = v_a_2006_;
v_isShared_2011_ = v_isSharedCheck_2043_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2008_);
lean_dec(v_a_2006_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2043_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_num_2012_; lean_object* v_den_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2042_; 
v_num_2012_ = lean_ctor_get(v_snd_2007_, 0);
v_den_2013_ = lean_ctor_get(v_snd_2007_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_snd_2007_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2015_ = v_snd_2007_;
v_isShared_2016_ = v_isSharedCheck_2042_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_den_2013_);
lean_inc(v_num_2012_);
lean_dec(v_snd_2007_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2042_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2008_);
v___x_2019_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 7);
lean_ctor_set(v___x_2015_, 1, v___x_2019_);
lean_ctor_set(v___x_2015_, 0, v___x_2018_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___y_2023_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_dec_eq(v_den_2013_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2035_ = l_Int_repr(v_num_2012_);
lean_dec(v_num_2012_);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2037_ = lean_string_append(v___x_2035_, v___x_2036_);
v___x_2038_ = l_Nat_reprFast(v_den_2013_);
v___x_2039_ = lean_string_append(v___x_2037_, v___x_2038_);
lean_dec_ref(v___x_2038_);
v___y_2023_ = v___x_2039_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2040_; 
lean_dec(v_den_2013_);
v___x_2040_ = l_Int_repr(v_num_2012_);
lean_dec(v_num_2012_);
v___y_2023_ = v___x_2040_;
goto v___jp_2022_;
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2023_);
v___x_2025_ = l_Lean_MessageData_ofFormat(v___x_2024_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 7);
lean_ctor_set(v___x_2010_, 1, v___x_2025_);
lean_ctor_set(v___x_2010_, 0, v___x_2021_);
v___x_2027_ = v___x_2010_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; 
lean_inc(v_traceClass_1994_);
v___x_2028_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_1994_, v___x_2027_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2028_) == 0)
{
size_t v___x_2029_; size_t v___x_2030_; 
lean_dec_ref_known(v___x_2028_, 1);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_1997_, v___x_2029_);
v_i_1997_ = v___x_2030_;
v_b_1998_ = v___x_2017_;
goto _start;
}
else
{
lean_dec(v_traceClass_1994_);
return v___x_2028_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2044_, lean_object* v_as_2045_, lean_object* v_sz_2046_, lean_object* v_i_2047_, lean_object* v_b_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
size_t v_sz_boxed_2054_; size_t v_i_boxed_2055_; lean_object* v_res_2056_; 
v_sz_boxed_2054_ = lean_unbox_usize(v_sz_2046_);
lean_dec(v_sz_2046_);
v_i_boxed_2055_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_res_2056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2044_, v_as_2045_, v_sz_boxed_2054_, v_i_boxed_2055_, v_b_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v_as_2045_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2060_, lean_object* v_model_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_options_2070_; uint8_t v_hasTrace_2071_; 
v_options_2070_ = lean_ctor_get(v_a_2064_, 2);
v_hasTrace_2071_ = lean_ctor_get_uint8(v_options_2070_, sizeof(void*)*1);
if (v_hasTrace_2071_ == 0)
{
lean_dec(v_traceClass_2060_);
goto v___jp_2067_;
}
else
{
lean_object* v_inheritedTraceOptions_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_inheritedTraceOptions_2072_ = lean_ctor_get(v_a_2064_, 13);
v___x_2073_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2060_);
v___x_2074_ = l_Lean_Name_append(v___x_2073_, v_traceClass_2060_);
v___x_2075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2072_, v_options_2070_, v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec(v_traceClass_2060_);
goto v___jp_2067_;
}
else
{
lean_object* v___x_2076_; size_t v_sz_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(0);
v_sz_2077_ = lean_array_size(v_model_2061_);
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2060_, v_model_2061_, v_sz_2077_, v___x_2078_, v___x_2076_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2079_, 0);
lean_dec(v_unused_2087_);
v___x_2081_ = v___x_2079_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_dec(v___x_2079_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2076_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
return v___x_2079_;
}
}
}
v___jp_2067_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2088_, lean_object* v_model_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2088_, v_model_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec_ref(v_model_2089_);
return v_res_2095_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
