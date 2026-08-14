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
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_nbuckets_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_550_ = lean_array_get_size(v_data_549_);
v___x_551_ = lean_unsigned_to_nat(2u);
v_nbuckets_552_ = lean_nat_mul(v___x_550_, v___x_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_box(0);
v___x_555_ = lean_mk_array(v_nbuckets_552_, v___x_554_);
v___x_556_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_553_, v_data_549_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_557_, lean_object* v_b_558_, lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_dec(v_b_558_);
lean_dec_ref(v_a_557_);
return v_x_559_;
}
else
{
lean_object* v_key_560_; lean_object* v_value_561_; lean_object* v_tail_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v_key_560_ = lean_ctor_get(v_x_559_, 0);
v_value_561_ = lean_ctor_get(v_x_559_, 1);
v_tail_562_ = lean_ctor_get(v_x_559_, 2);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_574_ == 0)
{
v___x_564_ = v_x_559_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_tail_562_);
lean_inc(v_value_561_);
lean_inc(v_key_560_);
lean_dec(v_x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_expr_eqv(v_key_560_, v_a_557_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_557_, v_b_558_, v_tail_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 2, v___x_567_);
v___x_569_ = v___x_564_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_key_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_value_561_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v___x_572_; 
lean_dec(v_value_561_);
lean_dec(v_key_560_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_b_558_);
lean_ctor_set(v___x_564_, 0, v_a_557_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_b_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_tail_562_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
uint8_t v___x_577_; 
v___x_577_ = 0;
return v___x_577_;
}
else
{
lean_object* v_key_578_; lean_object* v_tail_579_; uint8_t v___x_580_; 
v_key_578_ = lean_ctor_get(v_x_576_, 0);
v_tail_579_ = lean_ctor_get(v_x_576_, 2);
v___x_580_ = lean_expr_eqv(v_key_578_, v_a_575_);
if (v___x_580_ == 0)
{
v_x_576_ = v_tail_579_;
goto _start;
}
else
{
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_582_, lean_object* v_x_583_){
_start:
{
uint8_t v_res_584_; lean_object* v_r_585_; 
v_res_584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_582_, v_x_583_);
lean_dec(v_x_583_);
lean_dec_ref(v_a_582_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_586_, lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
lean_object* v_size_589_; lean_object* v_buckets_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_633_; 
v_size_589_ = lean_ctor_get(v_m_586_, 0);
v_buckets_590_ = lean_ctor_get(v_m_586_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_m_586_);
if (v_isSharedCheck_633_ == 0)
{
v___x_592_ = v_m_586_;
v_isShared_593_ = v_isSharedCheck_633_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_buckets_590_);
lean_inc(v_size_589_);
lean_dec(v_m_586_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_633_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v_fold_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v_bkt_607_; uint8_t v___x_608_; 
v___x_594_ = lean_array_get_size(v_buckets_590_);
v___x_595_ = l_Lean_Expr_hash(v_a_587_);
v___x_596_ = 32ULL;
v___x_597_ = lean_uint64_shift_right(v___x_595_, v___x_596_);
v_fold_598_ = lean_uint64_xor(v___x_595_, v___x_597_);
v___x_599_ = 16ULL;
v___x_600_ = lean_uint64_shift_right(v_fold_598_, v___x_599_);
v___x_601_ = lean_uint64_xor(v_fold_598_, v___x_600_);
v___x_602_ = lean_uint64_to_usize(v___x_601_);
v___x_603_ = lean_usize_of_nat(v___x_594_);
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_sub(v___x_603_, v___x_604_);
v___x_606_ = lean_usize_land(v___x_602_, v___x_605_);
v_bkt_607_ = lean_array_uget_borrowed(v_buckets_590_, v___x_606_);
v___x_608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_587_, v_bkt_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v_size_x27_610_; lean_object* v___x_611_; lean_object* v_buckets_x27_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v_size_x27_610_ = lean_nat_add(v_size_589_, v___x_609_);
lean_dec(v_size_589_);
lean_inc(v_bkt_607_);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v_a_587_);
lean_ctor_set(v___x_611_, 1, v_b_588_);
lean_ctor_set(v___x_611_, 2, v_bkt_607_);
v_buckets_x27_612_ = lean_array_uset(v_buckets_590_, v___x_606_, v___x_611_);
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_mul(v_size_x27_610_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_nat_div(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_array_get_size(v_buckets_x27_612_);
v___x_618_ = lean_nat_dec_le(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
if (v___x_618_ == 0)
{
lean_object* v_val_619_; lean_object* v___x_621_; 
v_val_619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_612_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_val_619_);
lean_ctor_set(v___x_592_, 0, v_size_x27_610_);
v___x_621_ = v___x_592_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_size_x27_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_val_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_624_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v_buckets_x27_612_);
lean_ctor_set(v___x_592_, 0, v_size_x27_610_);
v___x_624_ = v___x_592_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_size_x27_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_buckets_x27_612_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v___x_626_; lean_object* v_buckets_x27_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
lean_inc(v_bkt_607_);
v___x_626_ = lean_box(0);
v_buckets_x27_627_ = lean_array_uset(v_buckets_590_, v___x_606_, v___x_626_);
v___x_628_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_587_, v_b_588_, v_bkt_607_);
v___x_629_ = lean_array_uset(v_buckets_x27_627_, v___x_606_, v___x_628_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_629_);
v___x_631_ = v___x_592_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_size_589_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_634_, lean_object* v_as_x27_635_, lean_object* v_b_636_){
_start:
{
if (lean_obj_tag(v_as_x27_635_) == 0)
{
lean_dec_ref(v_v_634_);
return v_b_636_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_head_637_ = lean_ctor_get(v_as_x27_635_, 0);
v_tail_638_ = lean_ctor_get(v_as_x27_635_, 1);
lean_inc_ref(v_v_634_);
lean_inc(v_head_637_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_636_, v_head_637_, v_v_634_);
v_as_x27_635_ = v_tail_638_;
v_b_636_ = v___x_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_641_, lean_object* v_as_x27_642_, lean_object* v_b_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_641_, v_as_x27_642_, v_b_643_);
lean_dec(v_as_x27_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_645_, lean_object* v_e_646_, lean_object* v_v_647_, lean_object* v_a_648_){
_start:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = 0;
v___x_650_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_645_, v_e_646_, v___x_649_);
v___x_651_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_647_, v___x_650_, v_a_648_);
lean_dec(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_652_, lean_object* v_e_653_, lean_object* v_v_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_652_, v_e_653_, v_v_654_, v_a_655_);
lean_dec_ref(v_goal_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_657_, lean_object* v_m_658_, lean_object* v_a_659_, lean_object* v_b_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_658_, v_a_659_, v_b_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_662_, lean_object* v_as_663_, lean_object* v_as_x27_664_, lean_object* v_b_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_662_, v_as_x27_664_, v_b_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_668_, lean_object* v_as_669_, lean_object* v_as_x27_670_, lean_object* v_b_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_668_, v_as_669_, v_as_x27_670_, v_b_671_, v_a_672_);
lean_dec(v_as_x27_670_);
lean_dec(v_as_669_);
return v_res_673_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_678_, v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec_ref(v_a_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_683_, lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_686_, lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_687_, v_b_688_, v_x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_691_, lean_object* v_i_692_, lean_object* v_source_693_, lean_object* v_target_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_692_, v_source_693_, v_target_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_697_, v_x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_x_701_) == 0)
{
return v_x_700_;
}
else
{
lean_object* v_key_702_; lean_object* v_value_703_; lean_object* v_tail_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_741_; 
v_key_702_ = lean_ctor_get(v_x_701_, 0);
v_value_703_ = lean_ctor_get(v_x_701_, 1);
v_tail_704_ = lean_ctor_get(v_x_701_, 2);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_701_);
if (v_isSharedCheck_741_ == 0)
{
v___x_706_ = v_x_701_;
v_isShared_707_ = v_isSharedCheck_741_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_tail_704_);
lean_inc(v_value_703_);
lean_inc(v_key_702_);
lean_dec(v_x_701_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_741_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; uint64_t v___y_710_; lean_object* v_intZero_728_; uint8_t v_isNeg_729_; 
v___x_708_ = lean_array_get_size(v_x_700_);
v_intZero_728_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_729_ = lean_int_dec_lt(v_key_702_, v_intZero_728_);
if (v_isNeg_729_ == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint64_t v___x_733_; 
v_a_730_ = lean_nat_abs(v_key_702_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_nat_mul(v___x_731_, v_a_730_);
lean_dec(v_a_730_);
v___x_733_ = lean_uint64_of_nat(v___x_732_);
lean_dec(v___x_732_);
v___y_710_ = v___x_733_;
goto v___jp_709_;
}
else
{
lean_object* v_abs_734_; lean_object* v_one_735_; lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint64_t v___x_740_; 
v_abs_734_ = lean_nat_abs(v_key_702_);
v_one_735_ = lean_unsigned_to_nat(1u);
v_a_736_ = lean_nat_sub(v_abs_734_, v_one_735_);
lean_dec(v_abs_734_);
v___x_737_ = lean_unsigned_to_nat(2u);
v___x_738_ = lean_nat_mul(v___x_737_, v_a_736_);
lean_dec(v_a_736_);
v___x_739_ = lean_nat_add(v___x_738_, v_one_735_);
lean_dec(v___x_738_);
v___x_740_ = lean_uint64_of_nat(v___x_739_);
lean_dec(v___x_739_);
v___y_710_ = v___x_740_;
goto v___jp_709_;
}
v___jp_709_:
{
uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v_fold_713_; uint64_t v___x_714_; uint64_t v___x_715_; uint64_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_711_ = 32ULL;
v___x_712_ = lean_uint64_shift_right(v___y_710_, v___x_711_);
v_fold_713_ = lean_uint64_xor(v___y_710_, v___x_712_);
v___x_714_ = 16ULL;
v___x_715_ = lean_uint64_shift_right(v_fold_713_, v___x_714_);
v___x_716_ = lean_uint64_xor(v_fold_713_, v___x_715_);
v___x_717_ = lean_uint64_to_usize(v___x_716_);
v___x_718_ = lean_usize_of_nat(v___x_708_);
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_sub(v___x_718_, v___x_719_);
v___x_721_ = lean_usize_land(v___x_717_, v___x_720_);
v___x_722_ = lean_array_uget_borrowed(v_x_700_, v___x_721_);
lean_inc(v___x_722_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 2, v___x_722_);
v___x_724_ = v___x_706_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_key_702_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_value_703_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_722_);
v___x_724_ = v_reuseFailAlloc_727_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; 
v___x_725_ = lean_array_uset(v_x_700_, v___x_721_, v___x_724_);
v_x_700_ = v___x_725_;
v_x_701_ = v_tail_704_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_742_, lean_object* v_source_743_, lean_object* v_target_744_){
_start:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_source_743_);
v___x_746_ = lean_nat_dec_lt(v_i_742_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec_ref(v_source_743_);
lean_dec(v_i_742_);
return v_target_744_;
}
else
{
lean_object* v_es_747_; lean_object* v___x_748_; lean_object* v_source_749_; lean_object* v_target_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_es_747_ = lean_array_fget(v_source_743_, v_i_742_);
v___x_748_ = lean_box(0);
v_source_749_ = lean_array_fset(v_source_743_, v_i_742_, v___x_748_);
v_target_750_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_744_, v_es_747_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_i_742_, v___x_751_);
lean_dec(v_i_742_);
v_i_742_ = v___x_752_;
v_source_743_ = v_source_749_;
v_target_744_ = v_target_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_nbuckets_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_755_ = lean_array_get_size(v_data_754_);
v___x_756_ = lean_unsigned_to_nat(2u);
v_nbuckets_757_ = lean_nat_mul(v___x_755_, v___x_756_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_box(0);
v___x_760_ = lean_mk_array(v_nbuckets_757_, v___x_759_);
v___x_761_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_758_, v_data_754_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_762_, lean_object* v_a_763_, lean_object* v_b_764_){
_start:
{
lean_object* v_size_765_; lean_object* v_buckets_766_; lean_object* v___x_767_; uint64_t v___y_769_; lean_object* v_intZero_806_; uint8_t v_isNeg_807_; 
v_size_765_ = lean_ctor_get(v_m_762_, 0);
v_buckets_766_ = lean_ctor_get(v_m_762_, 1);
v___x_767_ = lean_array_get_size(v_buckets_766_);
v_intZero_806_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_807_ = lean_int_dec_lt(v_a_763_, v_intZero_806_);
if (v_isNeg_807_ == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint64_t v___x_811_; 
v_a_808_ = lean_nat_abs(v_a_763_);
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = lean_nat_mul(v___x_809_, v_a_808_);
lean_dec(v_a_808_);
v___x_811_ = lean_uint64_of_nat(v___x_810_);
lean_dec(v___x_810_);
v___y_769_ = v___x_811_;
goto v___jp_768_;
}
else
{
lean_object* v_abs_812_; lean_object* v_one_813_; lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint64_t v___x_818_; 
v_abs_812_ = lean_nat_abs(v_a_763_);
v_one_813_ = lean_unsigned_to_nat(1u);
v_a_814_ = lean_nat_sub(v_abs_812_, v_one_813_);
lean_dec(v_abs_812_);
v___x_815_ = lean_unsigned_to_nat(2u);
v___x_816_ = lean_nat_mul(v___x_815_, v_a_814_);
lean_dec(v_a_814_);
v___x_817_ = lean_nat_add(v___x_816_, v_one_813_);
lean_dec(v___x_816_);
v___x_818_ = lean_uint64_of_nat(v___x_817_);
lean_dec(v___x_817_);
v___y_769_ = v___x_818_;
goto v___jp_768_;
}
v___jp_768_:
{
uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v_fold_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v_bkt_781_; uint8_t v___x_782_; 
v___x_770_ = 32ULL;
v___x_771_ = lean_uint64_shift_right(v___y_769_, v___x_770_);
v_fold_772_ = lean_uint64_xor(v___y_769_, v___x_771_);
v___x_773_ = 16ULL;
v___x_774_ = lean_uint64_shift_right(v_fold_772_, v___x_773_);
v___x_775_ = lean_uint64_xor(v_fold_772_, v___x_774_);
v___x_776_ = lean_uint64_to_usize(v___x_775_);
v___x_777_ = lean_usize_of_nat(v___x_767_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_sub(v___x_777_, v___x_778_);
v___x_780_ = lean_usize_land(v___x_776_, v___x_779_);
v_bkt_781_ = lean_array_uget_borrowed(v_buckets_766_, v___x_780_);
v___x_782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_763_, v_bkt_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_803_; 
lean_inc_ref(v_buckets_766_);
lean_inc(v_size_765_);
v_isSharedCheck_803_ = !lean_is_exclusive(v_m_762_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; lean_object* v_unused_805_; 
v_unused_804_ = lean_ctor_get(v_m_762_, 1);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_m_762_, 0);
lean_dec(v_unused_805_);
v___x_784_ = v_m_762_;
v_isShared_785_ = v_isSharedCheck_803_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_m_762_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_803_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v_size_x27_787_; lean_object* v___x_788_; lean_object* v_buckets_x27_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_786_ = lean_unsigned_to_nat(1u);
v_size_x27_787_ = lean_nat_add(v_size_765_, v___x_786_);
lean_dec(v_size_765_);
lean_inc(v_bkt_781_);
v___x_788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_788_, 0, v_a_763_);
lean_ctor_set(v___x_788_, 1, v_b_764_);
lean_ctor_set(v___x_788_, 2, v_bkt_781_);
v_buckets_x27_789_ = lean_array_uset(v_buckets_766_, v___x_780_, v___x_788_);
v___x_790_ = lean_unsigned_to_nat(4u);
v___x_791_ = lean_nat_mul(v_size_x27_787_, v___x_790_);
v___x_792_ = lean_unsigned_to_nat(3u);
v___x_793_ = lean_nat_div(v___x_791_, v___x_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_array_get_size(v_buckets_x27_789_);
v___x_795_ = lean_nat_dec_le(v___x_793_, v___x_794_);
lean_dec(v___x_793_);
if (v___x_795_ == 0)
{
lean_object* v_val_796_; lean_object* v___x_798_; 
v_val_796_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_789_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_val_796_);
lean_ctor_set(v___x_784_, 0, v_size_x27_787_);
v___x_798_ = v___x_784_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_size_x27_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_val_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
lean_object* v___x_801_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_buckets_x27_789_);
lean_ctor_set(v___x_784_, 0, v_size_x27_787_);
v___x_801_ = v___x_784_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_size_x27_787_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_buckets_x27_789_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_dec(v_b_764_);
lean_dec(v_a_763_);
return v_m_762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_819_, lean_object* v_isTarget_820_, lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec_ref(v_isTarget_820_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_824_);
return v___x_831_;
}
else
{
lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_914_; 
v_snd_832_ = lean_ctor_get(v_b_824_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_b_824_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_b_824_, 0);
lean_dec(v_unused_915_);
v___x_834_ = v_b_824_;
v_isShared_835_ = v_isSharedCheck_914_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_dec(v_b_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_914_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
lean_inc(v_a_836_);
v___x_837_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_819_, v_a_836_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_snd_838_; lean_object* v_a_839_; lean_object* v_fst_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_904_; 
v_snd_838_ = lean_ctor_get(v_snd_832_, 1);
lean_inc(v_snd_838_);
v_a_839_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_837_, 1);
v_fst_840_ = lean_ctor_get(v_snd_832_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_snd_832_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v_snd_832_, 1);
lean_dec(v_unused_905_);
v___x_842_ = v_snd_832_;
v_isShared_843_ = v_isSharedCheck_904_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_fst_840_);
lean_dec(v_snd_832_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_904_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_903_; 
v_fst_844_ = lean_ctor_get(v_snd_838_, 0);
v_snd_845_ = lean_ctor_get(v_snd_838_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_snd_838_);
if (v_isSharedCheck_903_ == 0)
{
v___x_847_ = v_snd_838_;
v_isShared_848_ = v_isSharedCheck_903_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_inc(v_fst_844_);
lean_dec(v_snd_838_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_903_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v_a_851_; uint8_t v___x_858_; 
v___x_849_ = lean_box(0);
v___x_858_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_839_);
if (v___x_858_ == 0)
{
lean_object* v___x_860_; 
lean_dec(v_a_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_snd_845_);
lean_ctor_set(v___x_842_, 0, v_fst_844_);
v___x_860_ = v___x_842_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_845_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_860_);
lean_ctor_set(v___x_834_, 0, v_fst_840_);
v___x_862_ = v___x_834_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v_a_851_ = v___x_862_;
goto v___jp_850_;
}
}
}
else
{
lean_object* v___x_865_; 
lean_inc_ref(v_isTarget_820_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v_a_839_);
v___x_865_ = lean_apply_6(v_isTarget_820_, v_a_839_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, lean_box(0));
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; uint8_t v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_a_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_snd_845_);
lean_ctor_set(v___x_842_, 0, v_fst_844_);
v___x_869_ = v___x_842_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_snd_845_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_869_);
lean_ctor_set(v___x_834_, 0, v_fst_840_);
v___x_871_ = v___x_834_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_a_851_ = v___x_871_;
goto v___jp_850_;
}
}
}
else
{
lean_object* v_self_874_; lean_object* v___x_875_; 
v_self_874_ = lean_ctor_get(v_a_839_, 0);
lean_inc_ref(v_self_874_);
lean_dec(v_a_839_);
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_845_, v_self_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_876_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_819_, v_snd_845_, v_self_874_, v_fst_844_, v_fst_840_);
lean_inc_n(v___x_876_, 2);
v___x_877_ = l_Rat_ofInt(v___x_876_);
v___x_878_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_819_, v_self_874_, v___x_877_, v_snd_845_);
v___x_879_ = lean_box(0);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_844_, v___x_876_, v___x_879_);
v___x_881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_882_ = lean_int_add(v___x_876_, v___x_881_);
lean_dec(v___x_876_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_878_);
lean_ctor_set(v___x_842_, 0, v___x_880_);
v___x_884_ = v___x_842_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_878_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_884_);
lean_ctor_set(v___x_834_, 0, v___x_882_);
v___x_886_ = v___x_834_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v_a_851_ = v___x_886_;
goto v___jp_850_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref_known(v___x_875_, 1);
lean_dec_ref(v_self_874_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_snd_845_);
lean_ctor_set(v___x_842_, 0, v_fst_844_);
v___x_890_ = v___x_842_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_844_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_snd_845_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v___x_890_);
lean_ctor_set(v___x_834_, 0, v_fst_840_);
v___x_892_ = v___x_834_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
v_a_851_ = v___x_892_;
goto v___jp_850_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
lean_dec(v_fst_844_);
lean_del_object(v___x_842_);
lean_dec(v_fst_840_);
lean_dec(v_a_839_);
lean_del_object(v___x_834_);
lean_dec_ref(v_isTarget_820_);
v_a_895_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_865_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_865_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
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
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
v___jp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_a_851_);
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_853_ = v___x_847_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_851_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
size_t v___x_854_; size_t v___x_855_; 
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_823_, v___x_854_);
v_i_823_ = v___x_855_;
v_b_824_ = v___x_853_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_del_object(v___x_834_);
lean_dec(v_snd_832_);
lean_dec_ref(v_isTarget_820_);
v_a_906_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_837_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_837_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_916_, lean_object* v_isTarget_917_, lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
size_t v_sz_boxed_927_; size_t v_i_boxed_928_; lean_object* v_res_929_; 
v_sz_boxed_927_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_928_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_916_, v_isTarget_917_, v_as_918_, v_sz_boxed_927_, v_i_boxed_928_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_as_918_);
lean_dec_ref(v_goal_916_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_930_, lean_object* v_isTarget_931_, lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_isTarget_931_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_935_);
return v___x_942_;
}
else
{
lean_object* v_snd_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1025_; 
v_snd_943_ = lean_ctor_get(v_b_935_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_b_935_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_b_935_, 0);
lean_dec(v_unused_1026_);
v___x_945_ = v_b_935_;
v_isShared_946_ = v_isSharedCheck_1025_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_943_);
lean_dec(v_b_935_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1025_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_array_uget_borrowed(v_as_932_, v_i_934_);
lean_inc(v_a_947_);
v___x_948_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_930_, v_a_947_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_snd_949_; lean_object* v_a_950_; lean_object* v_fst_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1015_; 
v_snd_949_ = lean_ctor_get(v_snd_943_, 1);
lean_inc(v_snd_949_);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_948_, 1);
v_fst_951_ = lean_ctor_get(v_snd_943_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_snd_943_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_snd_943_, 1);
lean_dec(v_unused_1016_);
v___x_953_ = v_snd_943_;
v_isShared_954_ = v_isSharedCheck_1015_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_fst_951_);
lean_dec(v_snd_943_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1015_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1014_; 
v_fst_955_ = lean_ctor_get(v_snd_949_, 0);
v_snd_956_ = lean_ctor_get(v_snd_949_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_snd_949_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_958_ = v_snd_949_;
v_isShared_959_ = v_isSharedCheck_1014_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snd_956_);
lean_inc(v_fst_955_);
lean_dec(v_snd_949_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1014_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v_a_962_; uint8_t v___x_969_; 
v___x_960_ = lean_box(0);
v___x_969_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_950_);
if (v___x_969_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v_a_950_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_snd_956_);
lean_ctor_set(v___x_953_, 0, v_fst_955_);
v___x_971_ = v___x_953_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_snd_956_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_971_);
lean_ctor_set(v___x_945_, 0, v_fst_951_);
v___x_973_ = v___x_945_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v_a_962_ = v___x_973_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v___x_976_; 
lean_inc_ref(v_isTarget_931_);
lean_inc(v___y_939_);
lean_inc_ref(v___y_938_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v_a_950_);
v___x_976_ = lean_apply_6(v_isTarget_931_, v_a_950_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, lean_box(0));
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; uint8_t v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = lean_unbox(v_a_977_);
lean_dec(v_a_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_980_; 
lean_dec(v_a_950_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_snd_956_);
lean_ctor_set(v___x_953_, 0, v_fst_955_);
v___x_980_ = v___x_953_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_snd_956_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_980_);
lean_ctor_set(v___x_945_, 0, v_fst_951_);
v___x_982_ = v___x_945_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_962_ = v___x_982_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v_self_985_; lean_object* v___x_986_; 
v_self_985_ = lean_ctor_get(v_a_950_, 0);
lean_inc_ref(v_self_985_);
lean_dec(v_a_950_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_956_, v_self_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_987_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_930_, v_snd_956_, v_self_985_, v_fst_955_, v_fst_951_);
lean_inc_n(v___x_987_, 2);
v___x_988_ = l_Rat_ofInt(v___x_987_);
v___x_989_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_930_, v_self_985_, v___x_988_, v_snd_956_);
v___x_990_ = lean_box(0);
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_955_, v___x_987_, v___x_990_);
v___x_992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_993_ = lean_int_add(v___x_987_, v___x_992_);
lean_dec(v___x_987_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_989_);
lean_ctor_set(v___x_953_, 0, v___x_991_);
v___x_995_ = v___x_953_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_989_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_995_);
lean_ctor_set(v___x_945_, 0, v___x_993_);
v___x_997_ = v___x_945_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_a_962_ = v___x_997_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref_known(v___x_986_, 1);
lean_dec_ref(v_self_985_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_snd_956_);
lean_ctor_set(v___x_953_, 0, v_fst_955_);
v___x_1001_ = v___x_953_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_snd_956_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_1001_);
lean_ctor_set(v___x_945_, 0, v_fst_951_);
v___x_1003_ = v___x_945_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
v_a_962_ = v___x_1003_;
goto v___jp_961_;
}
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_del_object(v___x_958_);
lean_dec(v_snd_956_);
lean_dec(v_fst_955_);
lean_del_object(v___x_953_);
lean_dec(v_fst_951_);
lean_dec(v_a_950_);
lean_del_object(v___x_945_);
lean_dec_ref(v_isTarget_931_);
v_a_1006_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_976_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_976_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
v___jp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_a_962_);
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_a_962_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_934_, v___x_965_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_930_, v_isTarget_931_, v_as_932_, v_sz_933_, v___x_966_, v___x_964_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_967_;
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
lean_dec_ref(v_isTarget_931_);
v_a_1017_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_948_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_948_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1027_, lean_object* v_isTarget_1028_, lean_object* v_as_1029_, lean_object* v_sz_1030_, lean_object* v_i_1031_, lean_object* v_b_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1030_);
lean_dec(v_sz_1030_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1027_, v_isTarget_1028_, v_as_1029_, v_sz_boxed_1038_, v_i_boxed_1039_, v_b_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_as_1029_);
lean_dec_ref(v_goal_1027_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1041_, lean_object* v_isTarget_1042_, lean_object* v_as_1043_, size_t v_sz_1044_, size_t v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_lt(v_i_1045_, v_sz_1044_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v_isTarget_1042_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_b_1046_);
return v___x_1053_;
}
else
{
lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1136_; 
v_snd_1054_ = lean_ctor_get(v_b_1046_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_b_1046_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_b_1046_, 0);
lean_dec(v_unused_1137_);
v___x_1056_ = v_b_1046_;
v_isShared_1057_ = v_isSharedCheck_1136_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_dec(v_b_1046_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1136_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_a_1058_; lean_object* v___x_1059_; 
v_a_1058_ = lean_array_uget_borrowed(v_as_1043_, v_i_1045_);
lean_inc(v_a_1058_);
v___x_1059_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1041_, v_a_1058_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_snd_1060_; lean_object* v_a_1061_; lean_object* v_fst_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1126_; 
v_snd_1060_ = lean_ctor_get(v_snd_1054_, 1);
lean_inc(v_snd_1060_);
v_a_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1059_, 1);
v_fst_1062_ = lean_ctor_get(v_snd_1054_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_snd_1054_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_snd_1054_, 1);
lean_dec(v_unused_1127_);
v___x_1064_ = v_snd_1054_;
v_isShared_1065_ = v_isSharedCheck_1126_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_fst_1062_);
lean_dec(v_snd_1054_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1126_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1125_; 
v_fst_1066_ = lean_ctor_get(v_snd_1060_, 0);
v_snd_1067_ = lean_ctor_get(v_snd_1060_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_snd_1060_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1069_ = v_snd_1060_;
v_isShared_1070_ = v_isSharedCheck_1125_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_snd_1067_);
lean_inc(v_fst_1066_);
lean_dec(v_snd_1060_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1125_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v_a_1073_; uint8_t v___x_1080_; 
v___x_1071_ = lean_box(0);
v___x_1080_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1061_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_a_1061_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_snd_1067_);
lean_ctor_set(v___x_1064_, 0, v_fst_1066_);
v___x_1082_ = v___x_1064_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_fst_1066_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_snd_1067_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1082_);
lean_ctor_set(v___x_1056_, 0, v_fst_1062_);
v___x_1084_ = v___x_1056_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fst_1062_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v_a_1073_ = v___x_1084_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v___x_1087_; 
lean_inc_ref(v_isTarget_1042_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v_a_1061_);
v___x_1087_ = lean_apply_6(v_isTarget_1042_, v_a_1061_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; uint8_t v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = lean_unbox(v_a_1088_);
lean_dec(v_a_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1091_; 
lean_dec(v_a_1061_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_snd_1067_);
lean_ctor_set(v___x_1064_, 0, v_fst_1066_);
v___x_1091_ = v___x_1064_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_fst_1066_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_snd_1067_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1091_);
lean_ctor_set(v___x_1056_, 0, v_fst_1062_);
v___x_1093_ = v___x_1056_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_fst_1062_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_a_1073_ = v___x_1093_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v_self_1096_; lean_object* v___x_1097_; 
v_self_1096_ = lean_ctor_get(v_a_1061_, 0);
lean_inc_ref(v_self_1096_);
lean_dec(v_a_1061_);
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1067_, v_self_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1098_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1041_, v_snd_1067_, v_self_1096_, v_fst_1066_, v_fst_1062_);
lean_inc_n(v___x_1098_, 2);
v___x_1099_ = l_Rat_ofInt(v___x_1098_);
v___x_1100_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1041_, v_self_1096_, v___x_1099_, v_snd_1067_);
v___x_1101_ = lean_box(0);
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1066_, v___x_1098_, v___x_1101_);
v___x_1103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1104_ = lean_int_add(v___x_1098_, v___x_1103_);
lean_dec(v___x_1098_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___x_1100_);
lean_ctor_set(v___x_1064_, 0, v___x_1102_);
v___x_1106_ = v___x_1064_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1100_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1106_);
lean_ctor_set(v___x_1056_, 0, v___x_1104_);
v___x_1108_ = v___x_1056_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v_a_1073_ = v___x_1108_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1097_, 1);
lean_dec_ref(v_self_1096_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_snd_1067_);
lean_ctor_set(v___x_1064_, 0, v_fst_1066_);
v___x_1112_ = v___x_1064_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_fst_1066_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_snd_1067_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1112_);
lean_ctor_set(v___x_1056_, 0, v_fst_1062_);
v___x_1114_ = v___x_1056_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_fst_1062_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
v_a_1073_ = v___x_1114_;
goto v___jp_1072_;
}
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1069_);
lean_dec(v_snd_1067_);
lean_dec(v_fst_1066_);
lean_del_object(v___x_1064_);
lean_dec(v_fst_1062_);
lean_dec(v_a_1061_);
lean_del_object(v___x_1056_);
lean_dec_ref(v_isTarget_1042_);
v_a_1117_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1087_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1087_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
v___jp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 1, v_a_1073_);
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1075_ = v___x_1069_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_a_1073_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
size_t v___x_1076_; size_t v___x_1077_; 
v___x_1076_ = ((size_t)1ULL);
v___x_1077_ = lean_usize_add(v_i_1045_, v___x_1076_);
v_i_1045_ = v___x_1077_;
v_b_1046_ = v___x_1075_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1056_);
lean_dec(v_snd_1054_);
lean_dec_ref(v_isTarget_1042_);
v_a_1128_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1059_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1059_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1138_, lean_object* v_isTarget_1139_, lean_object* v_as_1140_, lean_object* v_sz_1141_, lean_object* v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1138_, v_isTarget_1139_, v_as_1140_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_as_1140_);
lean_dec_ref(v_goal_1138_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1152_, lean_object* v_isTarget_1153_, lean_object* v_as_1154_, size_t v_sz_1155_, size_t v_i_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1156_, v_sz_1155_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec_ref(v_isTarget_1153_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_b_1157_);
return v___x_1164_;
}
else
{
lean_object* v_snd_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1247_; 
v_snd_1165_ = lean_ctor_get(v_b_1157_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_b_1157_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_b_1157_, 0);
lean_dec(v_unused_1248_);
v___x_1167_ = v_b_1157_;
v_isShared_1168_ = v_isSharedCheck_1247_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snd_1165_);
lean_dec(v_b_1157_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1247_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_array_uget_borrowed(v_as_1154_, v_i_1156_);
lean_inc(v_a_1169_);
v___x_1170_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1152_, v_a_1169_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_snd_1171_; lean_object* v_a_1172_; lean_object* v_fst_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1237_; 
v_snd_1171_ = lean_ctor_get(v_snd_1165_, 1);
lean_inc(v_snd_1171_);
v_a_1172_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1170_, 1);
v_fst_1173_ = lean_ctor_get(v_snd_1165_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_snd_1165_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_snd_1165_, 1);
lean_dec(v_unused_1238_);
v___x_1175_ = v_snd_1165_;
v_isShared_1176_ = v_isSharedCheck_1237_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_fst_1173_);
lean_dec(v_snd_1165_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1237_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1236_; 
v_fst_1177_ = lean_ctor_get(v_snd_1171_, 0);
v_snd_1178_ = lean_ctor_get(v_snd_1171_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_snd_1171_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1180_ = v_snd_1171_;
v_isShared_1181_ = v_isSharedCheck_1236_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1177_);
lean_dec(v_snd_1171_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1236_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v_a_1184_; uint8_t v___x_1191_; 
v___x_1182_ = lean_box(0);
v___x_1191_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1172_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1193_; 
lean_dec(v_a_1172_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_snd_1178_);
lean_ctor_set(v___x_1175_, 0, v_fst_1177_);
v___x_1193_ = v___x_1175_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_fst_1177_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_snd_1178_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1193_);
lean_ctor_set(v___x_1167_, 0, v_fst_1173_);
v___x_1195_ = v___x_1167_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_fst_1173_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
v_a_1184_ = v___x_1195_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1198_; 
lean_inc_ref(v_isTarget_1153_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v_a_1172_);
v___x_1198_ = lean_apply_6(v_isTarget_1153_, v_a_1172_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1202_; 
lean_dec(v_a_1172_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_snd_1178_);
lean_ctor_set(v___x_1175_, 0, v_fst_1177_);
v___x_1202_ = v___x_1175_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_fst_1177_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_snd_1178_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1202_);
lean_ctor_set(v___x_1167_, 0, v_fst_1173_);
v___x_1204_ = v___x_1167_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_fst_1173_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v_a_1184_ = v___x_1204_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v_self_1207_; lean_object* v___x_1208_; 
v_self_1207_ = lean_ctor_get(v_a_1172_, 0);
lean_inc_ref(v_self_1207_);
lean_dec(v_a_1172_);
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1178_, v_self_1207_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1209_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1152_, v_snd_1178_, v_self_1207_, v_fst_1177_, v_fst_1173_);
lean_inc_n(v___x_1209_, 2);
v___x_1210_ = l_Rat_ofInt(v___x_1209_);
v___x_1211_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1152_, v_self_1207_, v___x_1210_, v_snd_1178_);
v___x_1212_ = lean_box(0);
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1177_, v___x_1209_, v___x_1212_);
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1215_ = lean_int_add(v___x_1209_, v___x_1214_);
lean_dec(v___x_1209_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1211_);
lean_ctor_set(v___x_1175_, 0, v___x_1213_);
v___x_1217_ = v___x_1175_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1211_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1217_);
lean_ctor_set(v___x_1167_, 0, v___x_1215_);
v___x_1219_ = v___x_1167_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_a_1184_ = v___x_1219_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1223_; 
lean_dec_ref_known(v___x_1208_, 1);
lean_dec_ref(v_self_1207_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_snd_1178_);
lean_ctor_set(v___x_1175_, 0, v_fst_1177_);
v___x_1223_ = v___x_1175_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_fst_1177_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_snd_1178_);
v___x_1223_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1223_);
lean_ctor_set(v___x_1167_, 0, v_fst_1173_);
v___x_1225_ = v___x_1167_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_fst_1173_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v_a_1184_ = v___x_1225_;
goto v___jp_1183_;
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_del_object(v___x_1180_);
lean_dec(v_snd_1178_);
lean_dec(v_fst_1177_);
lean_del_object(v___x_1175_);
lean_dec(v_fst_1173_);
lean_dec(v_a_1172_);
lean_del_object(v___x_1167_);
lean_dec_ref(v_isTarget_1153_);
v_a_1228_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1198_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1198_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
v___jp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1184_);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1186_ = v___x_1180_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1184_);
v___x_1186_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1156_, v___x_1187_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1152_, v_isTarget_1153_, v_as_1154_, v_sz_1155_, v___x_1188_, v___x_1186_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_del_object(v___x_1167_);
lean_dec(v_snd_1165_);
lean_dec_ref(v_isTarget_1153_);
v_a_1239_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1170_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1170_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1249_, lean_object* v_isTarget_1250_, lean_object* v_as_1251_, lean_object* v_sz_1252_, lean_object* v_i_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
size_t v_sz_boxed_1260_; size_t v_i_boxed_1261_; lean_object* v_res_1262_; 
v_sz_boxed_1260_ = lean_unbox_usize(v_sz_1252_);
lean_dec(v_sz_1252_);
v_i_boxed_1261_ = lean_unbox_usize(v_i_1253_);
lean_dec(v_i_1253_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1249_, v_isTarget_1250_, v_as_1251_, v_sz_boxed_1260_, v_i_boxed_1261_, v_b_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v_as_1251_);
lean_dec_ref(v_goal_1249_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1263_, lean_object* v_goal_1264_, lean_object* v_isTarget_1265_, lean_object* v_n_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
if (lean_obj_tag(v_n_1266_) == 0)
{
lean_object* v_cs_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; size_t v_sz_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v_cs_1273_ = lean_ctor_get(v_n_1266_, 0);
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v_b_1267_);
v_sz_1276_ = lean_array_size(v_cs_1273_);
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1263_, v_goal_1264_, v_isTarget_1265_, v_cs_1273_, v_sz_1276_, v___x_1277_, v___x_1275_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1293_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1293_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1293_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; 
v_fst_1283_ = lean_ctor_get(v_a_1279_, 0);
if (lean_obj_tag(v_fst_1283_) == 0)
{
lean_object* v_snd_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_snd_1284_ = lean_ctor_get(v_a_1279_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_a_1279_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_snd_1284_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1285_);
v___x_1287_ = v___x_1281_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1291_; 
lean_inc_ref(v_fst_1283_);
lean_dec(v_a_1279_);
v_val_1289_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v_fst_1283_, 1);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_val_1289_);
v___x_1291_ = v___x_1281_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_val_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1278_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1278_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_vs_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; size_t v_sz_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v_vs_1302_ = lean_ctor_get(v_n_1266_, 0);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v_b_1267_);
v_sz_1305_ = lean_array_size(v_vs_1302_);
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1264_, v_isTarget_1265_, v_vs_1302_, v_sz_1305_, v___x_1306_, v___x_1304_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_fst_1312_; 
v_fst_1312_ = lean_ctor_get(v_a_1308_, 0);
if (lean_obj_tag(v_fst_1312_) == 0)
{
lean_object* v_snd_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v_snd_1313_ = lean_ctor_get(v_a_1308_, 1);
lean_inc(v_snd_1313_);
lean_dec(v_a_1308_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_snd_1313_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1314_);
v___x_1316_ = v___x_1310_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1320_; 
lean_inc_ref(v_fst_1312_);
lean_dec(v_a_1308_);
v_val_1318_ = lean_ctor_get(v_fst_1312_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v_fst_1312_, 1);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_val_1318_);
v___x_1320_ = v___x_1310_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_val_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1307_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1307_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1331_, lean_object* v_goal_1332_, lean_object* v_isTarget_1333_, lean_object* v_as_1334_, size_t v_sz_1335_, size_t v_i_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1336_, v_sz_1335_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v_isTarget_1333_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1337_);
return v___x_1344_;
}
else
{
lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1379_; 
v_snd_1345_ = lean_ctor_get(v_b_1337_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_b_1337_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_b_1337_, 0);
lean_dec(v_unused_1380_);
v___x_1347_ = v_b_1337_;
v_isShared_1348_ = v_isSharedCheck_1379_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_dec(v_b_1337_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1379_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_array_uget_borrowed(v_as_1334_, v_i_1336_);
lean_inc(v_snd_1345_);
lean_inc_ref(v_isTarget_1333_);
v___x_1350_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1331_, v_goal_1332_, v_isTarget_1333_, v_a_1349_, v_snd_1345_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1370_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1370_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1370_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
if (lean_obj_tag(v_a_1351_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec_ref(v_isTarget_1333_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1351_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1355_);
v___x_1357_ = v___x_1347_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_snd_1345_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1357_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_del_object(v___x_1353_);
lean_dec(v_snd_1345_);
v_a_1362_ = lean_ctor_get(v_a_1351_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v_a_1351_, 1);
v___x_1363_ = lean_box(0);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_a_1362_);
lean_ctor_set(v___x_1347_, 0, v___x_1363_);
v___x_1365_ = v___x_1347_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1362_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
size_t v___x_1366_; size_t v___x_1367_; 
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1336_, v___x_1366_);
v_i_1336_ = v___x_1367_;
v_b_1337_ = v___x_1365_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_dec_ref(v_isTarget_1333_);
v_a_1371_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1350_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1350_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1381_, lean_object* v_goal_1382_, lean_object* v_isTarget_1383_, lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1381_, v_goal_1382_, v_isTarget_1383_, v_as_1384_, v_sz_boxed_1393_, v_i_boxed_1394_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_as_1384_);
lean_dec_ref(v_goal_1382_);
lean_dec_ref(v_init_1381_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1396_, lean_object* v_goal_1397_, lean_object* v_isTarget_1398_, lean_object* v_n_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1396_, v_goal_1397_, v_isTarget_1398_, v_n_1399_, v_b_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v_n_1399_);
lean_dec_ref(v_goal_1397_);
lean_dec_ref(v_init_1396_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1407_, lean_object* v_isTarget_1408_, lean_object* v_t_1409_, lean_object* v_init_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_root_1416_; lean_object* v_tail_1417_; lean_object* v___x_1418_; 
v_root_1416_ = lean_ctor_get(v_t_1409_, 0);
v_tail_1417_ = lean_ctor_get(v_t_1409_, 1);
lean_inc_ref(v_isTarget_1408_);
lean_inc_ref(v_init_1410_);
v___x_1418_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1410_, v_goal_1407_, v_isTarget_1408_, v_root_1416_, v_init_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v_init_1410_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1455_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1455_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1455_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
if (lean_obj_tag(v_a_1419_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; 
lean_dec_ref(v_isTarget_1408_);
v_a_1423_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v_a_1419_, 1);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v_a_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; size_t v_sz_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
lean_del_object(v___x_1421_);
v_a_1427_ = lean_ctor_get(v_a_1419_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v_a_1419_, 1);
v___x_1428_ = lean_box(0);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v_a_1427_);
v_sz_1430_ = lean_array_size(v_tail_1417_);
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1407_, v_isTarget_1408_, v_tail_1417_, v_sz_1430_, v___x_1431_, v___x_1429_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1446_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1446_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1446_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_fst_1437_; 
v_fst_1437_ = lean_ctor_get(v_a_1433_, 0);
if (lean_obj_tag(v_fst_1437_) == 0)
{
lean_object* v_snd_1438_; lean_object* v___x_1440_; 
v_snd_1438_ = lean_ctor_get(v_a_1433_, 1);
lean_inc(v_snd_1438_);
lean_dec(v_a_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_snd_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_snd_1438_);
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
lean_object* v_val_1442_; lean_object* v___x_1444_; 
lean_inc_ref(v_fst_1437_);
lean_dec(v_a_1433_);
v_val_1442_ = lean_ctor_get(v_fst_1437_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v_fst_1437_, 1);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_val_1442_);
v___x_1444_ = v___x_1435_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_val_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1432_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1432_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v_isTarget_1408_);
v_a_1456_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1418_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1418_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1464_, lean_object* v_isTarget_1465_, lean_object* v_t_1466_, lean_object* v_init_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1464_, v_isTarget_1465_, v_t_1466_, v_init_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec_ref(v_t_1466_);
lean_dec_ref(v_goal_1464_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1475_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
else
{
lean_object* v_value_1479_; lean_object* v_tail_1480_; lean_object* v_num_1481_; lean_object* v_den_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_value_1479_ = lean_ctor_get(v_a_1474_, 1);
lean_inc(v_value_1479_);
v_tail_1480_ = lean_ctor_get(v_a_1474_, 2);
lean_inc(v_tail_1480_);
lean_dec_ref_known(v_a_1474_, 3);
v_num_1481_ = lean_ctor_get(v_value_1479_, 0);
lean_inc(v_num_1481_);
v_den_1482_ = lean_ctor_get(v_value_1479_, 1);
lean_inc(v_den_1482_);
lean_dec(v_value_1479_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_nat_dec_eq(v_den_1482_, v___x_1483_);
lean_dec(v_den_1482_);
if (v___x_1484_ == 0)
{
lean_dec(v_num_1481_);
v_a_1474_ = v_tail_1480_;
goto _start;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1475_, v_num_1481_, v___x_1486_);
v_a_1474_ = v_tail_1480_;
v_a_1475_ = v___x_1487_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1489_, v_a_1490_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_b_1496_);
return v___x_1503_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_array_uget_borrowed(v_as_1493_, v_i_1495_);
lean_inc(v_a_1504_);
v___x_1505_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1504_, v_b_1496_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1518_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1518_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
if (lean_obj_tag(v_a_1506_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; 
v_a_1510_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v_a_1506_, 1);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v_a_1510_);
v___x_1512_ = v___x_1508_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
else
{
lean_object* v_a_1514_; size_t v___x_1515_; size_t v___x_1516_; 
lean_del_object(v___x_1508_);
v_a_1514_ = lean_ctor_get(v_a_1506_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v_a_1506_, 1);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_i_1495_, v___x_1515_);
v_i_1495_ = v___x_1516_;
v_b_1496_ = v_a_1514_;
goto _start;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_a_1519_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1505_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1505_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1527_, lean_object* v_sz_1528_, lean_object* v_i_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1528_);
lean_dec(v_sz_1528_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1529_);
lean_dec(v_i_1529_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1527_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_as_1527_);
return v_res_1538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_unsigned_to_nat(16u);
v___x_1541_ = lean_mk_array(v___x_1540_, v___x_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_used_1544_; 
v___x_1542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1543_ = lean_unsigned_to_nat(0u);
v_used_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1544_, 0, v___x_1543_);
lean_ctor_set(v_used_1544_, 1, v___x_1542_);
return v_used_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1545_, lean_object* v_isTarget_1546_, lean_object* v_model_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v_buckets_1553_; lean_object* v_used_1554_; size_t v_sz_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v_buckets_1553_ = lean_ctor_get(v_model_1547_, 1);
v_used_1554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1555_ = lean_array_size(v_buckets_1553_);
v___x_1556_ = ((size_t)0ULL);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1553_, v_sz_1555_, v___x_1556_, v_used_1554_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_toGoalState_1558_; lean_object* v_a_1559_; lean_object* v_exprs_1560_; lean_object* v_nextVal_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_toGoalState_1558_ = lean_ctor_get(v_goal_1545_, 0);
v_a_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1557_, 1);
v_exprs_1560_ = lean_ctor_get(v_toGoalState_1558_, 2);
v_nextVal_1561_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1559_);
lean_ctor_set(v___x_1562_, 1, v_model_1547_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_nextVal_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1545_, v_isTarget_1546_, v_exprs_1560_, v___x_1563_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1574_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1574_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1574_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_snd_1569_; lean_object* v_snd_1570_; lean_object* v___x_1572_; 
v_snd_1569_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_a_1565_);
v_snd_1570_ = lean_ctor_get(v_snd_1569_, 1);
lean_inc(v_snd_1570_);
lean_dec(v_snd_1569_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_snd_1570_);
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_snd_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1564_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1564_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_model_1547_);
lean_dec_ref(v_isTarget_1546_);
v_a_1583_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1557_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1557_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1591_, lean_object* v_isTarget_1592_, lean_object* v_model_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1591_, v_isTarget_1592_, v_model_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec_ref(v_goal_1591_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1600_, lean_object* v_m_1601_, lean_object* v_a_1602_, lean_object* v_b_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1601_, v_a_1602_, v_b_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1605_, v_a_1606_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1613_, v_a_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1621_, lean_object* v_data_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1624_, lean_object* v_i_1625_, lean_object* v_source_1626_, lean_object* v_target_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1625_, v_source_1626_, v_target_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1633_, lean_object* v_hi_1634_, lean_object* v_pivot_1635_, lean_object* v_as_1636_, lean_object* v_i_1637_, lean_object* v_k_1638_){
_start:
{
uint8_t v___y_1640_; uint8_t v___x_1649_; 
v___x_1649_ = lean_nat_dec_lt(v_k_1638_, v_hi_1634_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v_k_1638_);
v___x_1650_ = lean_array_fswap(v_as_1636_, v_i_1637_, v_hi_1634_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_i_1637_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v_fst_1653_; lean_object* v_fst_1654_; lean_object* v_g_u2081_1655_; lean_object* v_g_u2082_1656_; uint8_t v___x_1657_; 
v___x_1652_ = lean_array_fget_borrowed(v_as_1636_, v_k_1638_);
v_fst_1653_ = lean_ctor_get(v___x_1652_, 0);
v_fst_1654_ = lean_ctor_get(v_pivot_1635_, 0);
v_g_u2081_1655_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1633_, v_fst_1653_);
v_g_u2082_1656_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1633_, v_fst_1654_);
v___x_1657_ = lean_nat_dec_eq(v_g_u2081_1655_, v_g_u2082_1656_);
if (v___x_1657_ == 0)
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_nat_dec_lt(v_g_u2081_1655_, v_g_u2082_1656_);
lean_dec(v_g_u2082_1656_);
lean_dec(v_g_u2081_1655_);
v___y_1640_ = v___x_1658_;
goto v___jp_1639_;
}
else
{
uint8_t v___x_1659_; 
lean_dec(v_g_u2082_1656_);
lean_dec(v_g_u2081_1655_);
v___x_1659_ = lean_expr_lt(v_fst_1653_, v_fst_1654_);
v___y_1640_ = v___x_1659_;
goto v___jp_1639_;
}
}
v___jp_1639_:
{
if (v___y_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v_k_1638_, v___x_1641_);
lean_dec(v_k_1638_);
v_k_1638_ = v___x_1642_;
goto _start;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1644_ = lean_array_fswap(v_as_1636_, v_i_1637_, v_k_1638_);
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_nat_add(v_i_1637_, v___x_1645_);
lean_dec(v_i_1637_);
v___x_1647_ = lean_nat_add(v_k_1638_, v___x_1645_);
lean_dec(v_k_1638_);
v_as_1636_ = v___x_1644_;
v_i_1637_ = v___x_1646_;
v_k_1638_ = v___x_1647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1660_, lean_object* v_hi_1661_, lean_object* v_pivot_1662_, lean_object* v_as_1663_, lean_object* v_i_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1660_, v_hi_1661_, v_pivot_1662_, v_as_1663_, v_i_1664_, v_k_1665_);
lean_dec_ref(v_pivot_1662_);
lean_dec(v_hi_1661_);
lean_dec_ref(v_goal_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_fst_1670_; lean_object* v_fst_1671_; lean_object* v_g_u2081_1672_; lean_object* v_g_u2082_1673_; uint8_t v___x_1674_; 
v_fst_1670_ = lean_ctor_get(v_x_1668_, 0);
v_fst_1671_ = lean_ctor_get(v_x_1669_, 0);
v_g_u2081_1672_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1667_, v_fst_1670_);
v_g_u2082_1673_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1667_, v_fst_1671_);
v___x_1674_ = lean_nat_dec_eq(v_g_u2081_1672_, v_g_u2082_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_nat_dec_lt(v_g_u2081_1672_, v_g_u2082_1673_);
lean_dec(v_g_u2082_1673_);
lean_dec(v_g_u2081_1672_);
return v___x_1675_;
}
else
{
uint8_t v___x_1676_; 
lean_dec(v_g_u2082_1673_);
lean_dec(v_g_u2081_1672_);
v___x_1676_ = lean_expr_lt(v_fst_1670_, v_fst_1671_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1677_, v_x_1678_, v_x_1679_);
lean_dec_ref(v_x_1679_);
lean_dec_ref(v_x_1678_);
lean_dec_ref(v_goal_1677_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1682_, lean_object* v_n_1683_, lean_object* v_as_1684_, lean_object* v_lo_1685_, lean_object* v_hi_1686_){
_start:
{
lean_object* v___y_1688_; uint8_t v___x_1698_; 
v___x_1698_ = lean_nat_dec_lt(v_lo_1685_, v_hi_1686_);
if (v___x_1698_ == 0)
{
lean_dec(v_lo_1685_);
return v_as_1684_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_mid_1701_; lean_object* v___y_1703_; lean_object* v___y_1709_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1699_ = lean_nat_add(v_lo_1685_, v_hi_1686_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v_mid_1701_ = lean_nat_shiftr(v___x_1699_, v___x_1700_);
lean_dec(v___x_1699_);
v___x_1714_ = lean_array_fget_borrowed(v_as_1684_, v_mid_1701_);
v___x_1715_ = lean_array_fget_borrowed(v_as_1684_, v_lo_1685_);
v___x_1716_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1682_, v___x_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
v___y_1709_ = v_as_1684_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_array_fswap(v_as_1684_, v_lo_1685_, v_mid_1701_);
v___y_1709_ = v___x_1717_;
goto v___jp_1708_;
}
v___jp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_array_fget_borrowed(v___y_1703_, v_mid_1701_);
v___x_1705_ = lean_array_fget_borrowed(v___y_1703_, v_hi_1686_);
v___x_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1682_, v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v_mid_1701_);
v___y_1688_ = v___y_1703_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_array_fswap(v___y_1703_, v_mid_1701_, v_hi_1686_);
lean_dec(v_mid_1701_);
v___y_1688_ = v___x_1707_;
goto v___jp_1687_;
}
}
v___jp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = lean_array_fget_borrowed(v___y_1709_, v_hi_1686_);
v___x_1711_ = lean_array_fget_borrowed(v___y_1709_, v_lo_1685_);
v___x_1712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1682_, v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
v___y_1703_ = v___y_1709_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_array_fswap(v___y_1709_, v_lo_1685_, v_hi_1686_);
v___y_1703_ = v___x_1713_;
goto v___jp_1702_;
}
}
}
v___jp_1687_:
{
lean_object* v_pivot_1689_; lean_object* v___x_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; uint8_t v___x_1693_; 
v_pivot_1689_ = lean_array_fget(v___y_1688_, v_hi_1686_);
lean_inc_n(v_lo_1685_, 2);
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1682_, v_hi_1686_, v_pivot_1689_, v___y_1688_, v_lo_1685_, v_lo_1685_);
lean_dec(v_pivot_1689_);
v_fst_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_fst_1691_);
v_snd_1692_ = lean_ctor_get(v___x_1690_, 1);
lean_inc(v_snd_1692_);
lean_dec_ref(v___x_1690_);
v___x_1693_ = lean_nat_dec_le(v_hi_1686_, v_fst_1691_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1682_, v_n_1683_, v_snd_1692_, v_lo_1685_, v_fst_1691_);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_add(v_fst_1691_, v___x_1695_);
lean_dec(v_fst_1691_);
v_as_1684_ = v___x_1694_;
v_lo_1685_ = v___x_1696_;
goto _start;
}
else
{
lean_dec(v_fst_1691_);
lean_dec(v_lo_1685_);
return v_snd_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1718_, lean_object* v_n_1719_, lean_object* v_as_1720_, lean_object* v_lo_1721_, lean_object* v_hi_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1718_, v_n_1719_, v_as_1720_, v_lo_1721_, v_hi_1722_);
lean_dec(v_hi_1722_);
lean_dec(v_n_1719_);
lean_dec_ref(v_goal_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1724_, lean_object* v_m_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = lean_array_get_size(v_m_1725_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_nat_dec_eq(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___y_1732_; uint8_t v___x_1736_; 
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_sub(v___x_1726_, v___x_1729_);
v___x_1736_ = lean_nat_dec_le(v___x_1727_, v___x_1730_);
if (v___x_1736_ == 0)
{
lean_inc(v___x_1730_);
v___y_1732_ = v___x_1730_;
goto v___jp_1731_;
}
else
{
v___y_1732_ = v___x_1727_;
goto v___jp_1731_;
}
v___jp_1731_:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_nat_dec_le(v___y_1732_, v___x_1730_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v___x_1730_);
lean_inc(v___y_1732_);
v___x_1734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1724_, v___x_1726_, v_m_1725_, v___y_1732_, v___y_1732_);
lean_dec(v___y_1732_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1724_, v___x_1726_, v_m_1725_, v___y_1732_, v___x_1730_);
lean_dec(v___x_1730_);
return v___x_1735_;
}
}
}
else
{
return v_m_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1737_, lean_object* v_m_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1737_, v_m_1738_);
lean_dec_ref(v_goal_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1740_, lean_object* v_n_1741_, lean_object* v_as_1742_, lean_object* v_lo_1743_, lean_object* v_hi_1744_, lean_object* v_w_1745_, lean_object* v_hlo_1746_, lean_object* v_hhi_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1740_, v_n_1741_, v_as_1742_, v_lo_1743_, v_hi_1744_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1749_, lean_object* v_n_1750_, lean_object* v_as_1751_, lean_object* v_lo_1752_, lean_object* v_hi_1753_, lean_object* v_w_1754_, lean_object* v_hlo_1755_, lean_object* v_hhi_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1749_, v_n_1750_, v_as_1751_, v_lo_1752_, v_hi_1753_, v_w_1754_, v_hlo_1755_, v_hhi_1756_);
lean_dec(v_hi_1753_);
lean_dec(v_n_1750_);
lean_dec_ref(v_goal_1749_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1758_, lean_object* v_n_1759_, lean_object* v_lo_1760_, lean_object* v_hi_1761_, lean_object* v_hhi_1762_, lean_object* v_pivot_1763_, lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_k_1766_, lean_object* v_ilo_1767_, lean_object* v_ik_1768_, lean_object* v_w_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1758_, v_hi_1761_, v_pivot_1763_, v_as_1764_, v_i_1765_, v_k_1766_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1771_, lean_object* v_n_1772_, lean_object* v_lo_1773_, lean_object* v_hi_1774_, lean_object* v_hhi_1775_, lean_object* v_pivot_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v_k_1779_, lean_object* v_ilo_1780_, lean_object* v_ik_1781_, lean_object* v_w_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1771_, v_n_1772_, v_lo_1773_, v_hi_1774_, v_hhi_1775_, v_pivot_1776_, v_as_1777_, v_i_1778_, v_k_1779_, v_ilo_1780_, v_ik_1781_, v_w_1782_);
lean_dec_ref(v_pivot_1776_);
lean_dec(v_hi_1774_);
lean_dec(v_lo_1773_);
lean_dec(v_n_1772_);
lean_dec_ref(v_goal_1771_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
if (lean_obj_tag(v_a_1784_) == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1785_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v_key_1789_; lean_object* v_value_1790_; lean_object* v_tail_1791_; uint8_t v___x_1792_; 
v_key_1789_ = lean_ctor_get(v_a_1784_, 0);
lean_inc_n(v_key_1789_, 2);
v_value_1790_ = lean_ctor_get(v_a_1784_, 1);
lean_inc(v_value_1790_);
v_tail_1791_ = lean_ctor_get(v_a_1784_, 2);
lean_inc(v_tail_1791_);
lean_dec_ref_known(v_a_1784_, 3);
v___x_1792_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1789_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_key_1789_);
lean_ctor_set(v___x_1793_, 1, v_value_1790_);
v___x_1794_ = lean_array_push(v_a_1785_, v___x_1793_);
v_a_1784_ = v_tail_1791_;
v_a_1785_ = v___x_1794_;
goto _start;
}
else
{
lean_dec(v_value_1790_);
lean_dec(v_key_1789_);
v_a_1784_ = v_tail_1791_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1797_, v_a_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1801_, size_t v_sz_1802_, size_t v_i_1803_, lean_object* v_b_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_usize_dec_lt(v_i_1803_, v_sz_1802_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_b_1804_);
return v___x_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_array_uget_borrowed(v_as_1801_, v_i_1803_);
lean_inc(v_a_1812_);
v___x_1813_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1812_, v_b_1804_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1826_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1826_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
if (lean_obj_tag(v_a_1814_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; 
v_a_1818_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v_a_1814_, 1);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_a_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
else
{
lean_object* v_a_1822_; size_t v___x_1823_; size_t v___x_1824_; 
lean_del_object(v___x_1816_);
v_a_1822_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v_a_1814_, 1);
v___x_1823_ = ((size_t)1ULL);
v___x_1824_ = lean_usize_add(v_i_1803_, v___x_1823_);
v_i_1803_ = v___x_1824_;
v_b_1804_ = v_a_1822_;
goto _start;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_a_1827_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1813_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1813_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1835_, lean_object* v_sz_1836_, lean_object* v_i_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
size_t v_sz_boxed_1844_; size_t v_i_boxed_1845_; lean_object* v_res_1846_; 
v_sz_boxed_1844_ = lean_unbox_usize(v_sz_1836_);
lean_dec(v_sz_1836_);
v_i_boxed_1845_ = lean_unbox_usize(v_i_1837_);
lean_dec(v_i_1837_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1835_, v_sz_boxed_1844_, v_i_boxed_1845_, v_b_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_as_1835_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1849_, lean_object* v_isTarget_1850_, lean_object* v_model_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1849_, v_isTarget_1850_, v_model_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_buckets_1859_; lean_object* v___x_1860_; size_t v_sz_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v_buckets_1859_ = lean_ctor_get(v_a_1858_, 1);
lean_inc_ref(v_buckets_1859_);
lean_dec(v_a_1858_);
v___x_1860_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1861_ = lean_array_size(v_buckets_1859_);
v___x_1862_ = ((size_t)0ULL);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1859_, v_sz_1861_, v___x_1862_, v___x_1860_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec_ref(v_buckets_1859_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1872_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1849_, v_a_1864_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
return v___x_1863_;
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1857_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1857_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1881_, lean_object* v_isTarget_1882_, lean_object* v_model_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1881_, v_isTarget_1882_, v_model_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_goal_1881_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1890_, v_a_1891_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1898_, v_a_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v_env_1913_; lean_object* v___x_1914_; lean_object* v_mctx_1915_; lean_object* v_lctx_1916_; lean_object* v_options_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1912_ = lean_st_ref_get(v___y_1910_);
v_env_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_ref(v_env_1913_);
lean_dec(v___x_1912_);
v___x_1914_ = lean_st_ref_get(v___y_1908_);
v_mctx_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_mctx_1915_);
lean_dec(v___x_1914_);
v_lctx_1916_ = lean_ctor_get(v___y_1907_, 2);
v_options_1917_ = lean_ctor_get(v___y_1909_, 2);
lean_inc_ref(v_options_1917_);
lean_inc_ref(v_lctx_1916_);
v___x_1918_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1918_, 0, v_env_1913_);
lean_ctor_set(v___x_1918_, 1, v_mctx_1915_);
lean_ctor_set(v___x_1918_, 2, v_lctx_1916_);
lean_ctor_set(v___x_1918_, 3, v_options_1917_);
v___x_1919_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_msgData_1906_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1927_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1928_; double v___x_1929_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = lean_float_of_nat(v___x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1933_, lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_ref_1940_; lean_object* v___x_1941_; lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1986_; 
v_ref_1940_ = lean_ctor_get(v___y_1937_, 5);
v___x_1941_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1986_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1986_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v_traceState_1947_; lean_object* v_env_1948_; lean_object* v_nextMacroScope_1949_; lean_object* v_ngen_1950_; lean_object* v_auxDeclNGen_1951_; lean_object* v_cache_1952_; lean_object* v_messages_1953_; lean_object* v_infoState_1954_; lean_object* v_snapshotTasks_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1985_; 
v___x_1946_ = lean_st_ref_take(v___y_1938_);
v_traceState_1947_ = lean_ctor_get(v___x_1946_, 4);
v_env_1948_ = lean_ctor_get(v___x_1946_, 0);
v_nextMacroScope_1949_ = lean_ctor_get(v___x_1946_, 1);
v_ngen_1950_ = lean_ctor_get(v___x_1946_, 2);
v_auxDeclNGen_1951_ = lean_ctor_get(v___x_1946_, 3);
v_cache_1952_ = lean_ctor_get(v___x_1946_, 5);
v_messages_1953_ = lean_ctor_get(v___x_1946_, 6);
v_infoState_1954_ = lean_ctor_get(v___x_1946_, 7);
v_snapshotTasks_1955_ = lean_ctor_get(v___x_1946_, 8);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1957_ = v___x_1946_;
v_isShared_1958_ = v_isSharedCheck_1985_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_snapshotTasks_1955_);
lean_inc(v_infoState_1954_);
lean_inc(v_messages_1953_);
lean_inc(v_cache_1952_);
lean_inc(v_traceState_1947_);
lean_inc(v_auxDeclNGen_1951_);
lean_inc(v_ngen_1950_);
lean_inc(v_nextMacroScope_1949_);
lean_inc(v_env_1948_);
lean_dec(v___x_1946_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1985_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
uint64_t v_tid_1959_; lean_object* v_traces_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1984_; 
v_tid_1959_ = lean_ctor_get_uint64(v_traceState_1947_, sizeof(void*)*1);
v_traces_1960_ = lean_ctor_get(v_traceState_1947_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_traceState_1947_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1962_ = v_traceState_1947_;
v_isShared_1963_ = v_isSharedCheck_1984_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_traces_1960_);
lean_dec(v_traceState_1947_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1984_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; double v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1966_ = 0;
v___x_1967_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1968_, 0, v_cls_1933_);
lean_ctor_set(v___x_1968_, 1, v___x_1964_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3, v___x_1965_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3 + 8, v___x_1965_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 16, v___x_1966_);
v___x_1969_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1970_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v_a_1942_);
lean_ctor_set(v___x_1970_, 2, v___x_1969_);
lean_inc(v_ref_1940_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_ref_1940_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_PersistentArray_push___redArg(v_traces_1960_, v___x_1971_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1972_);
v___x_1974_ = v___x_1962_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1972_);
lean_ctor_set_uint64(v_reuseFailAlloc_1983_, sizeof(void*)*1, v_tid_1959_);
v___x_1974_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1976_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 4, v___x_1974_);
v___x_1976_ = v___x_1957_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_env_1948_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_nextMacroScope_1949_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_ngen_1950_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_auxDeclNGen_1951_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1982_, 5, v_cache_1952_);
lean_ctor_set(v_reuseFailAlloc_1982_, 6, v_messages_1953_);
lean_ctor_set(v_reuseFailAlloc_1982_, 7, v_infoState_1954_);
lean_ctor_set(v_reuseFailAlloc_1982_, 8, v_snapshotTasks_1955_);
v___x_1976_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_st_ref_put(v___y_1938_, v___x_1976_);
v___x_1978_ = lean_box(0);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1978_);
v___x_1980_ = v___x_1944_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1987_, lean_object* v_msg_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1987_, v_msg_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1994_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_1997_ = l_Lean_stringToMessageData(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_1999_, lean_object* v_as_2000_, size_t v_sz_2001_, size_t v_i_2002_, lean_object* v_b_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_lt(v_i_2002_, v_sz_2001_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_traceClass_1999_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_b_2003_);
return v___x_2010_;
}
else
{
lean_object* v_a_2011_; lean_object* v_snd_2012_; lean_object* v_fst_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2048_; 
v_a_2011_ = lean_array_uget(v_as_2000_, v_i_2002_);
v_snd_2012_ = lean_ctor_get(v_a_2011_, 1);
v_fst_2013_ = lean_ctor_get(v_a_2011_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2015_ = v_a_2011_;
v_isShared_2016_ = v_isSharedCheck_2048_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2012_);
lean_inc(v_fst_2013_);
lean_dec(v_a_2011_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2048_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_num_2017_; lean_object* v_den_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2047_; 
v_num_2017_ = lean_ctor_get(v_snd_2012_, 0);
v_den_2018_ = lean_ctor_get(v_snd_2012_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_snd_2012_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2020_ = v_snd_2012_;
v_isShared_2021_ = v_isSharedCheck_2047_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_den_2018_);
lean_inc(v_num_2017_);
lean_dec(v_snd_2012_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2047_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2013_);
v___x_2024_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 7);
lean_ctor_set(v___x_2020_, 1, v___x_2024_);
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___y_2028_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_dec_eq(v_den_2018_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = l_Int_repr(v_num_2017_);
lean_dec(v_num_2017_);
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
v___x_2043_ = l_Nat_reprFast(v_den_2018_);
v___x_2044_ = lean_string_append(v___x_2042_, v___x_2043_);
lean_dec_ref(v___x_2043_);
v___y_2028_ = v___x_2044_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2045_; 
lean_dec(v_den_2018_);
v___x_2045_ = l_Int_repr(v_num_2017_);
lean_dec(v_num_2017_);
v___y_2028_ = v___x_2045_;
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___y_2028_);
v___x_2030_ = l_Lean_MessageData_ofFormat(v___x_2029_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 7);
lean_ctor_set(v___x_2015_, 1, v___x_2030_);
lean_ctor_set(v___x_2015_, 0, v___x_2026_);
v___x_2032_ = v___x_2015_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
lean_inc(v_traceClass_1999_);
v___x_2033_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_1999_, v___x_2032_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2033_) == 0)
{
size_t v___x_2034_; size_t v___x_2035_; 
lean_dec_ref_known(v___x_2033_, 1);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_add(v_i_2002_, v___x_2034_);
v_i_2002_ = v___x_2035_;
v_b_2003_ = v___x_2022_;
goto _start;
}
else
{
lean_dec(v_traceClass_1999_);
return v___x_2033_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2049_, lean_object* v_as_2050_, lean_object* v_sz_2051_, lean_object* v_i_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_sz_boxed_2059_; size_t v_i_boxed_2060_; lean_object* v_res_2061_; 
v_sz_boxed_2059_ = lean_unbox_usize(v_sz_2051_);
lean_dec(v_sz_2051_);
v_i_boxed_2060_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2049_, v_as_2050_, v_sz_boxed_2059_, v_i_boxed_2060_, v_b_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_as_2050_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2065_, lean_object* v_model_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_options_2075_; uint8_t v_hasTrace_2076_; 
v_options_2075_ = lean_ctor_get(v_a_2069_, 2);
v_hasTrace_2076_ = lean_ctor_get_uint8(v_options_2075_, sizeof(void*)*1);
if (v_hasTrace_2076_ == 0)
{
lean_dec(v_traceClass_2065_);
goto v___jp_2072_;
}
else
{
lean_object* v_inheritedTraceOptions_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_inheritedTraceOptions_2077_ = lean_ctor_get(v_a_2069_, 13);
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2065_);
v___x_2079_ = l_Lean_Name_append(v___x_2078_, v_traceClass_2065_);
v___x_2080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2077_, v_options_2075_, v___x_2079_);
lean_dec(v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v_traceClass_2065_);
goto v___jp_2072_;
}
else
{
lean_object* v___x_2081_; size_t v_sz_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(0);
v_sz_2082_ = lean_array_size(v_model_2066_);
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2065_, v_model_2066_, v_sz_2082_, v___x_2083_, v___x_2081_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
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
v___jp_2072_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
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
