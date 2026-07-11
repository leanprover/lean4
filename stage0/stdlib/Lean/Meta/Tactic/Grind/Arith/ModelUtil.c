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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v_val_40_; lean_object* v___x_41_; uint8_t v___x_42_; uint8_t v___x_43_; 
v_val_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v___x_39_, 1);
v___x_41_ = l_Rat_ofInt(v_v_37_);
v___x_42_ = l_instDecidableEqRat_decEq(v_val_40_, v___x_41_);
lean_dec_ref(v___x_41_);
lean_dec(v_val_40_);
v___x_43_ = lean_bool_not(v___x_42_);
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
lean_dec(v___x_39_);
lean_dec(v_v_37_);
v___x_44_ = 1;
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq___boxed(lean_object* v_a_45_, lean_object* v_v_46_, lean_object* v_other_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_45_, v_v_46_, v_other_47_);
lean_dec_ref(v_other_47_);
lean_dec_ref(v_a_45_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(lean_object* v_00_u03b2_50_, lean_object* v_m_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_m_51_, v_a_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___boxed(lean_object* v_00_u03b2_54_, lean_object* v_m_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0(v_00_u03b2_54_, v_m_55_, v_a_56_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_m_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(lean_object* v_00_u03b2_58_, lean_object* v_a_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___redArg(v_a_59_, v_x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0___boxed(lean_object* v_00_u03b2_62_, lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0_spec__0(v_00_u03b2_62_, v_a_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec_ref(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(lean_object* v_goal_81_, lean_object* v_e_82_, lean_object* v_a_83_, lean_object* v_v_84_, lean_object* v_as_x27_85_, lean_object* v_b_86_){
_start:
{
if (lean_obj_tag(v_as_x27_85_) == 0)
{
lean_dec(v_v_84_);
lean_inc_ref(v_b_86_);
return v_b_86_;
}
else
{
lean_object* v_head_87_; lean_object* v_tail_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___y_92_; uint8_t v___y_93_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_head_87_ = lean_ctor_get(v_as_x27_85_, 0);
v_tail_88_ = lean_ctor_get(v_as_x27_85_, 1);
v___x_89_ = lean_box(0);
v___x_90_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_87_);
v___x_98_ = l_Lean_Expr_cleanupAnnotations(v_head_87_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_dec_ref(v___x_98_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v_arg_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_arg_101_ = lean_ctor_get(v___x_98_, 1);
lean_inc_ref(v_arg_101_);
v___x_102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
v___x_103_ = l_Lean_Expr_isApp(v___x_102_);
if (v___x_103_ == 0)
{
lean_dec_ref(v___x_102_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v_arg_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_105_ = lean_ctor_get(v___x_102_, 1);
lean_inc_ref(v_arg_105_);
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_102_);
v___x_107_ = l_Lean_Expr_isApp(v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v___x_106_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_106_);
v___x_110_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_111_ = l_Lean_Expr_isConstOf(v___x_109_, v___x_110_);
lean_dec_ref(v___x_109_);
if (v___x_111_ == 0)
{
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_81_, v_head_87_);
if (lean_obj_tag(v___x_113_) == 1)
{
lean_object* v_val_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_val_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_116_ = l_Lean_Expr_isConstOf(v_val_114_, v___x_115_);
lean_dec(v_val_114_);
if (v___x_116_ == 0)
{
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_81_, v_arg_105_);
lean_dec_ref(v_arg_105_);
if (lean_obj_tag(v___x_118_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_120_; 
v_val_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_val_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_81_, v_arg_101_);
lean_dec_ref(v_arg_101_);
if (lean_obj_tag(v___x_120_) == 1)
{
lean_object* v_val_121_; uint8_t v___y_123_; uint8_t v___x_128_; 
v_val_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_128_ = lean_expr_eqv(v_val_119_, v_e_82_);
if (v___x_128_ == 0)
{
v___y_123_ = v___x_128_;
goto v___jp_122_;
}
else
{
uint8_t v___x_129_; uint8_t v___x_130_; 
lean_inc(v_v_84_);
v___x_129_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_83_, v_v_84_, v_val_121_);
v___x_130_ = lean_bool_not(v___x_129_);
v___y_123_ = v___x_130_;
goto v___jp_122_;
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_expr_eqv(v_val_121_, v_e_82_);
lean_dec(v_val_121_);
if (v___x_124_ == 0)
{
lean_dec(v_val_119_);
v___y_92_ = v___y_123_;
v___y_93_ = v___x_124_;
goto v___jp_91_;
}
else
{
uint8_t v___x_125_; uint8_t v___x_126_; 
lean_inc(v_v_84_);
v___x_125_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_83_, v_v_84_, v_val_119_);
lean_dec(v_val_119_);
v___x_126_ = lean_bool_not(v___x_125_);
v___y_92_ = v___y_123_;
v___y_93_ = v___x_126_;
goto v___jp_91_;
}
}
else
{
lean_object* v___x_127_; 
lean_dec(v_val_121_);
lean_dec(v_val_119_);
lean_dec(v_v_84_);
v___x_127_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6));
return v___x_127_;
}
}
}
else
{
lean_dec(v___x_120_);
lean_dec(v_val_119_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
}
else
{
lean_dec(v___x_118_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
}
}
else
{
lean_dec(v___x_113_);
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_101_);
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
}
}
}
}
v___jp_91_:
{
if (v___y_93_ == 0)
{
v_as_x27_85_ = v_tail_88_;
v_b_86_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_v_84_);
v___x_95_ = lean_box(v___y_92_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_89_);
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_134_, lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_v_137_, lean_object* v_as_x27_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_134_, v_e_135_, v_a_136_, v_v_137_, v_as_x27_138_, v_b_139_);
lean_dec_ref(v_b_139_);
lean_dec(v_as_x27_138_);
lean_dec_ref(v_a_136_);
lean_dec_ref(v_e_135_);
lean_dec_ref(v_goal_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_141_, lean_object* v_vals_142_, lean_object* v_i_143_, lean_object* v_k_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_array_get_size(v_keys_141_);
v___x_146_ = lean_nat_dec_lt(v_i_143_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; 
lean_dec(v_i_143_);
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_k_x27_148_; uint8_t v___x_149_; 
v_k_x27_148_ = lean_array_fget_borrowed(v_keys_141_, v_i_143_);
v___x_149_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_144_, v_k_x27_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_i_143_, v___x_150_);
lean_dec(v_i_143_);
v_i_143_ = v___x_151_;
goto _start;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_array_fget_borrowed(v_vals_142_, v_i_143_);
lean_dec(v_i_143_);
lean_inc(v___x_153_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_155_, lean_object* v_vals_156_, lean_object* v_i_157_, lean_object* v_k_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_155_, v_vals_156_, v_i_157_, v_k_158_);
lean_dec_ref(v_k_158_);
lean_dec_ref(v_vals_156_);
lean_dec_ref(v_keys_155_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_160_, size_t v_x_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v_es_163_; lean_object* v___x_164_; size_t v___x_165_; size_t v___x_166_; lean_object* v_j_167_; lean_object* v___x_168_; 
v_es_163_ = lean_ctor_get(v_x_160_, 0);
v___x_164_ = lean_box(2);
v___x_165_ = ((size_t)31ULL);
v___x_166_ = lean_usize_land(v_x_161_, v___x_165_);
v_j_167_ = lean_usize_to_nat(v___x_166_);
v___x_168_ = lean_array_get_borrowed(v___x_164_, v_es_163_, v_j_167_);
lean_dec(v_j_167_);
switch(lean_obj_tag(v___x_168_))
{
case 0:
{
lean_object* v_key_169_; lean_object* v_val_170_; uint8_t v___x_171_; 
v_key_169_ = lean_ctor_get(v___x_168_, 0);
v_val_170_ = lean_ctor_get(v___x_168_, 1);
v___x_171_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_162_, v_key_169_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
lean_inc(v_val_170_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_val_170_);
return v___x_173_;
}
}
case 1:
{
lean_object* v_node_174_; size_t v___x_175_; size_t v___x_176_; 
v_node_174_ = lean_ctor_get(v___x_168_, 0);
v___x_175_ = ((size_t)5ULL);
v___x_176_ = lean_usize_shift_right(v_x_161_, v___x_175_);
v_x_160_ = v_node_174_;
v_x_161_ = v___x_176_;
goto _start;
}
default: 
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
}
else
{
lean_object* v_ks_179_; lean_object* v_vs_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_ks_179_ = lean_ctor_get(v_x_160_, 0);
v_vs_180_ = lean_ctor_get(v_x_160_, 1);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_179_, v_vs_180_, v___x_181_, v_x_162_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
size_t v_x_2525__boxed_186_; lean_object* v_res_187_; 
v_x_2525__boxed_186_ = lean_unbox_usize(v_x_184_);
lean_dec(v_x_184_);
v_res_187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_183_, v_x_2525__boxed_186_, v_x_185_);
lean_dec_ref(v_x_185_);
lean_dec_ref(v_x_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
uint64_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_188_, v___x_191_, v_x_189_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_193_, v_x_194_);
lean_dec_ref(v_x_194_);
lean_dec_ref(v_x_193_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_196_, lean_object* v_a_197_, lean_object* v_e_198_, lean_object* v_v_199_){
_start:
{
lean_object* v_toGoalState_200_; lean_object* v_parents_201_; lean_object* v___x_202_; 
v_toGoalState_200_ = lean_ctor_get(v_goal_196_, 0);
v_parents_201_ = lean_ctor_get(v_toGoalState_200_, 3);
v___x_202_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_201_, v_e_198_);
if (lean_obj_tag(v___x_202_) == 1)
{
lean_object* v_val_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_fst_207_; 
v_val_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_203_);
lean_dec(v_val_203_);
v___x_205_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_206_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_196_, v_e_198_, v_a_197_, v_v_199_, v___x_204_, v___x_205_);
lean_dec(v___x_204_);
v_fst_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_fst_207_);
lean_dec_ref(v___x_206_);
if (lean_obj_tag(v_fst_207_) == 0)
{
uint8_t v___x_208_; 
v___x_208_ = 1;
return v___x_208_;
}
else
{
lean_object* v_val_209_; uint8_t v___x_210_; 
v_val_209_ = lean_ctor_get(v_fst_207_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v_fst_207_, 1);
v___x_210_ = lean_unbox(v_val_209_);
lean_dec(v_val_209_);
return v___x_210_;
}
}
else
{
uint8_t v___x_211_; 
lean_dec(v___x_202_);
lean_dec(v_v_199_);
v___x_211_ = 1;
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_212_, lean_object* v_a_213_, lean_object* v_e_214_, lean_object* v_v_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_212_, v_a_213_, v_e_214_, v_v_215_);
lean_dec_ref(v_e_214_);
lean_dec_ref(v_a_213_);
lean_dec_ref(v_goal_212_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_219_, v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_222_, v_x_223_, v_x_224_);
lean_dec_ref(v_x_224_);
lean_dec_ref(v_x_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_226_, lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_v_229_, lean_object* v_as_230_, lean_object* v_as_x27_231_, lean_object* v_b_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_226_, v_e_227_, v_a_228_, v_v_229_, v_as_x27_231_, v_b_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_235_, lean_object* v_e_236_, lean_object* v_a_237_, lean_object* v_v_238_, lean_object* v_as_239_, lean_object* v_as_x27_240_, lean_object* v_b_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_235_, v_e_236_, v_a_237_, v_v_238_, v_as_239_, v_as_x27_240_, v_b_241_, v_a_242_);
lean_dec_ref(v_b_241_);
lean_dec(v_as_x27_240_);
lean_dec(v_as_239_);
lean_dec_ref(v_a_237_);
lean_dec_ref(v_e_236_);
lean_dec_ref(v_goal_235_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_244_, lean_object* v_x_245_, size_t v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_245_, v_x_246_, v_x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_2620__boxed_253_; lean_object* v_res_254_; 
v_x_2620__boxed_253_ = lean_unbox_usize(v_x_251_);
lean_dec(v_x_251_);
v_res_254_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_249_, v_x_250_, v_x_2620__boxed_253_, v_x_252_);
lean_dec_ref(v_x_252_);
lean_dec_ref(v_x_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_255_, lean_object* v_keys_256_, lean_object* v_vals_257_, lean_object* v_heq_258_, lean_object* v_i_259_, lean_object* v_k_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_256_, v_vals_257_, v_i_259_, v_k_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_262_, lean_object* v_keys_263_, lean_object* v_vals_264_, lean_object* v_heq_265_, lean_object* v_i_266_, lean_object* v_k_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_262_, v_keys_263_, v_vals_264_, v_heq_265_, v_i_266_, v_k_267_);
lean_dec_ref(v_k_267_);
lean_dec_ref(v_vals_264_);
lean_dec_ref(v_keys_263_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_a_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
else
{
lean_object* v_key_272_; lean_object* v_tail_273_; uint8_t v___x_274_; 
v_key_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 2);
v___x_274_ = lean_int_dec_eq(v_key_272_, v_a_269_);
if (v___x_274_ == 0)
{
v_x_270_ = v_tail_273_;
goto _start;
}
else
{
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_276_, v_x_277_);
lean_dec(v_x_277_);
lean_dec(v_a_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_280_; lean_object* v_intZero_281_; 
v_natZero_280_ = lean_unsigned_to_nat(0u);
v_intZero_281_ = lean_nat_to_int(v_natZero_280_);
return v_intZero_281_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_buckets_284_; lean_object* v___x_285_; uint64_t v___y_287_; lean_object* v_intZero_301_; uint8_t v_isNeg_302_; 
v_buckets_284_ = lean_ctor_get(v_m_282_, 1);
v___x_285_ = lean_array_get_size(v_buckets_284_);
v_intZero_301_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_302_ = lean_int_dec_lt(v_a_283_, v_intZero_301_);
if (v_isNeg_302_ == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint64_t v___x_306_; 
v_a_303_ = lean_nat_abs(v_a_283_);
v___x_304_ = lean_unsigned_to_nat(2u);
v___x_305_ = lean_nat_mul(v___x_304_, v_a_303_);
lean_dec(v_a_303_);
v___x_306_ = lean_uint64_of_nat(v___x_305_);
lean_dec(v___x_305_);
v___y_287_ = v___x_306_;
goto v___jp_286_;
}
else
{
lean_object* v_abs_307_; lean_object* v_one_308_; lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint64_t v___x_313_; 
v_abs_307_ = lean_nat_abs(v_a_283_);
v_one_308_ = lean_unsigned_to_nat(1u);
v_a_309_ = lean_nat_sub(v_abs_307_, v_one_308_);
lean_dec(v_abs_307_);
v___x_310_ = lean_unsigned_to_nat(2u);
v___x_311_ = lean_nat_mul(v___x_310_, v_a_309_);
lean_dec(v_a_309_);
v___x_312_ = lean_nat_add(v___x_311_, v_one_308_);
lean_dec(v___x_311_);
v___x_313_ = lean_uint64_of_nat(v___x_312_);
lean_dec(v___x_312_);
v___y_287_ = v___x_313_;
goto v___jp_286_;
}
v___jp_286_:
{
uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v_fold_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_288_ = 32ULL;
v___x_289_ = lean_uint64_shift_right(v___y_287_, v___x_288_);
v_fold_290_ = lean_uint64_xor(v___y_287_, v___x_289_);
v___x_291_ = 16ULL;
v___x_292_ = lean_uint64_shift_right(v_fold_290_, v___x_291_);
v___x_293_ = lean_uint64_xor(v_fold_290_, v___x_292_);
v___x_294_ = lean_uint64_to_usize(v___x_293_);
v___x_295_ = lean_usize_of_nat(v___x_285_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = lean_usize_sub(v___x_295_, v___x_296_);
v___x_298_ = lean_usize_land(v___x_294_, v___x_297_);
v___x_299_ = lean_array_uget_borrowed(v_buckets_284_, v___x_298_);
v___x_300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_283_, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_m_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_320_, lean_object* v_a_321_, lean_object* v_e_322_, lean_object* v_alreadyUsed_323_, lean_object* v_next_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_323_, v_next_324_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
lean_inc(v_next_324_);
v___x_326_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_320_, v_a_321_, v_e_322_, v_next_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_328_ = lean_int_add(v_next_324_, v___x_327_);
lean_dec(v_next_324_);
v_next_324_ = v___x_328_;
goto _start;
}
else
{
return v_next_324_;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_331_ = lean_int_add(v_next_324_, v___x_330_);
lean_dec(v_next_324_);
v_next_324_ = v___x_331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_333_, lean_object* v_a_334_, lean_object* v_e_335_, lean_object* v_alreadyUsed_336_, lean_object* v_next_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_333_, v_a_334_, v_e_335_, v_alreadyUsed_336_, v_next_337_);
lean_dec_ref(v_alreadyUsed_336_);
lean_dec_ref(v_e_335_);
lean_dec_ref(v_a_334_);
lean_dec_ref(v_goal_333_);
return v_res_338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_339_, lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_340_, v_a_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_343_, lean_object* v_m_344_, lean_object* v_a_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_343_, v_m_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_m_344_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_348_, lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_349_, v_x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_352_, lean_object* v_a_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_352_, v_a_353_, v_x_354_);
lean_dec(v_x_354_);
lean_dec(v_a_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_357_, lean_object* v_a_358_, lean_object* v_e_359_, lean_object* v_next_360_, lean_object* v_alreadyUsed_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_357_, v_a_358_, v_e_359_, v_alreadyUsed_361_, v_next_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_363_, lean_object* v_a_364_, lean_object* v_e_365_, lean_object* v_next_366_, lean_object* v_alreadyUsed_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_363_, v_a_364_, v_e_365_, v_next_366_, v_alreadyUsed_367_);
lean_dec_ref(v_alreadyUsed_367_);
lean_dec_ref(v_e_365_);
lean_dec_ref(v_a_364_);
lean_dec_ref(v_goal_363_);
return v_res_368_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_452_){
_start:
{
uint8_t v___y_454_; uint8_t v___x_489_; 
lean_inc_ref(v_e_452_);
v___x_489_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_452_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
lean_inc_ref(v_e_452_);
v___x_490_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_452_);
v___y_454_ = v___x_490_;
goto v___jp_453_;
}
else
{
v___y_454_ = v___x_489_;
goto v___jp_453_;
}
v___jp_453_:
{
if (v___y_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_456_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5));
v___x_458_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8));
v___x_460_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11));
v___x_462_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14));
v___x_464_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17));
v___x_466_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20));
v___x_468_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23));
v___x_470_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26));
v___x_472_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29));
v___x_474_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32));
v___x_476_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_475_);
if (v___x_476_ == 0)
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Expr_isIte(v_e_452_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_Expr_isDIte(v_e_452_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35));
v___x_480_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_482_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_484_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47));
v___x_486_ = l_Lean_Expr_isAppOf(v_e_452_, v___x_485_);
if (v___x_486_ == 0)
{
if (lean_obj_tag(v_e_452_) == 9)
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v_e_452_, 0);
lean_inc_ref(v_a_487_);
lean_dec_ref_known(v_e_452_, 1);
if (lean_obj_tag(v_a_487_) == 0)
{
uint8_t v___x_488_; 
lean_dec_ref_known(v_a_487_, 1);
v___x_488_ = 1;
return v___x_488_;
}
else
{
lean_dec_ref(v_a_487_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_484_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_480_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_476_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_474_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_472_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_470_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_468_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_466_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_464_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_462_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_460_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_458_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___x_456_;
}
}
else
{
lean_dec_ref(v_e_452_);
return v___y_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
return v_x_494_;
}
else
{
lean_object* v_key_496_; lean_object* v_value_497_; lean_object* v_tail_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_521_; 
v_key_496_ = lean_ctor_get(v_x_495_, 0);
v_value_497_ = lean_ctor_get(v_x_495_, 1);
v_tail_498_ = lean_ctor_get(v_x_495_, 2);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_521_ == 0)
{
v___x_500_ = v_x_495_;
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_tail_498_);
lean_inc(v_value_497_);
lean_inc(v_key_496_);
lean_dec(v_x_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; uint64_t v_fold_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_502_ = lean_array_get_size(v_x_494_);
v___x_503_ = l_Lean_Expr_hash(v_key_496_);
v___x_504_ = 32ULL;
v___x_505_ = lean_uint64_shift_right(v___x_503_, v___x_504_);
v_fold_506_ = lean_uint64_xor(v___x_503_, v___x_505_);
v___x_507_ = 16ULL;
v___x_508_ = lean_uint64_shift_right(v_fold_506_, v___x_507_);
v___x_509_ = lean_uint64_xor(v_fold_506_, v___x_508_);
v___x_510_ = lean_uint64_to_usize(v___x_509_);
v___x_511_ = lean_usize_of_nat(v___x_502_);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_sub(v___x_511_, v___x_512_);
v___x_514_ = lean_usize_land(v___x_510_, v___x_513_);
v___x_515_ = lean_array_uget_borrowed(v_x_494_, v___x_514_);
lean_inc(v___x_515_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 2, v___x_515_);
v___x_517_ = v___x_500_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_key_496_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_value_497_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v___x_515_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_array_uset(v_x_494_, v___x_514_, v___x_517_);
v_x_494_ = v___x_518_;
v_x_495_ = v_tail_498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_522_, lean_object* v_source_523_, lean_object* v_target_524_){
_start:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_source_523_);
v___x_526_ = lean_nat_dec_lt(v_i_522_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_source_523_);
lean_dec(v_i_522_);
return v_target_524_;
}
else
{
lean_object* v_es_527_; lean_object* v___x_528_; lean_object* v_source_529_; lean_object* v_target_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_es_527_ = lean_array_fget(v_source_523_, v_i_522_);
v___x_528_ = lean_box(0);
v_source_529_ = lean_array_fset(v_source_523_, v_i_522_, v___x_528_);
v_target_530_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_524_, v_es_527_);
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_i_522_, v___x_531_);
lean_dec(v_i_522_);
v_i_522_ = v___x_532_;
v_source_523_ = v_source_529_;
v_target_524_ = v_target_530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_nbuckets_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_535_ = lean_array_get_size(v_data_534_);
v___x_536_ = lean_unsigned_to_nat(2u);
v_nbuckets_537_ = lean_nat_mul(v___x_535_, v___x_536_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_box(0);
v___x_540_ = lean_mk_array(v_nbuckets_537_, v___x_539_);
v___x_541_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_538_, v_data_534_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_dec(v_b_543_);
lean_dec_ref(v_a_542_);
return v_x_544_;
}
else
{
lean_object* v_key_545_; lean_object* v_value_546_; lean_object* v_tail_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_559_; 
v_key_545_ = lean_ctor_get(v_x_544_, 0);
v_value_546_ = lean_ctor_get(v_x_544_, 1);
v_tail_547_ = lean_ctor_get(v_x_544_, 2);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_559_ == 0)
{
v___x_549_ = v_x_544_;
v_isShared_550_ = v_isSharedCheck_559_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_tail_547_);
lean_inc(v_value_546_);
lean_inc(v_key_545_);
lean_dec(v_x_544_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_559_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_expr_eqv(v_key_545_, v_a_542_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_542_, v_b_543_, v_tail_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_key_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_value_546_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v_value_546_);
lean_dec(v_key_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v_b_543_);
lean_ctor_set(v___x_549_, 0, v_a_542_);
v___x_557_ = v___x_549_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_542_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_b_543_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_tail_547_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
else
{
lean_object* v_key_563_; lean_object* v_tail_564_; uint8_t v___x_565_; 
v_key_563_ = lean_ctor_get(v_x_561_, 0);
v_tail_564_ = lean_ctor_get(v_x_561_, 2);
v___x_565_ = lean_expr_eqv(v_key_563_, v_a_560_);
if (v___x_565_ == 0)
{
v_x_561_ = v_tail_564_;
goto _start;
}
else
{
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_567_, lean_object* v_x_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_567_, v_x_568_);
lean_dec(v_x_568_);
lean_dec_ref(v_a_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v_size_574_; lean_object* v_buckets_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_618_; 
v_size_574_ = lean_ctor_get(v_m_571_, 0);
v_buckets_575_ = lean_ctor_get(v_m_571_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_m_571_);
if (v_isSharedCheck_618_ == 0)
{
v___x_577_ = v_m_571_;
v_isShared_578_ = v_isSharedCheck_618_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_buckets_575_);
lean_inc(v_size_574_);
lean_dec(v_m_571_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_618_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint64_t v___x_580_; uint64_t v___x_581_; uint64_t v___x_582_; uint64_t v_fold_583_; uint64_t v___x_584_; uint64_t v___x_585_; uint64_t v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; lean_object* v_bkt_592_; uint8_t v___x_593_; 
v___x_579_ = lean_array_get_size(v_buckets_575_);
v___x_580_ = l_Lean_Expr_hash(v_a_572_);
v___x_581_ = 32ULL;
v___x_582_ = lean_uint64_shift_right(v___x_580_, v___x_581_);
v_fold_583_ = lean_uint64_xor(v___x_580_, v___x_582_);
v___x_584_ = 16ULL;
v___x_585_ = lean_uint64_shift_right(v_fold_583_, v___x_584_);
v___x_586_ = lean_uint64_xor(v_fold_583_, v___x_585_);
v___x_587_ = lean_uint64_to_usize(v___x_586_);
v___x_588_ = lean_usize_of_nat(v___x_579_);
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_sub(v___x_588_, v___x_589_);
v___x_591_ = lean_usize_land(v___x_587_, v___x_590_);
v_bkt_592_ = lean_array_uget_borrowed(v_buckets_575_, v___x_591_);
v___x_593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_572_, v_bkt_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v_size_x27_595_; lean_object* v___x_596_; lean_object* v_buckets_x27_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v_size_x27_595_ = lean_nat_add(v_size_574_, v___x_594_);
lean_dec(v_size_574_);
lean_inc(v_bkt_592_);
v___x_596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_596_, 0, v_a_572_);
lean_ctor_set(v___x_596_, 1, v_b_573_);
lean_ctor_set(v___x_596_, 2, v_bkt_592_);
v_buckets_x27_597_ = lean_array_uset(v_buckets_575_, v___x_591_, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(4u);
v___x_599_ = lean_nat_mul(v_size_x27_595_, v___x_598_);
v___x_600_ = lean_unsigned_to_nat(3u);
v___x_601_ = lean_nat_div(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_array_get_size(v_buckets_x27_597_);
v___x_603_ = lean_nat_dec_le(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
if (v___x_603_ == 0)
{
lean_object* v_val_604_; lean_object* v___x_606_; 
v_val_604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_597_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_val_604_);
lean_ctor_set(v___x_577_, 0, v_size_x27_595_);
v___x_606_ = v___x_577_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_size_x27_595_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_val_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_609_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_buckets_x27_597_);
lean_ctor_set(v___x_577_, 0, v_size_x27_595_);
v___x_609_ = v___x_577_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_size_x27_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_buckets_x27_597_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v___x_611_; lean_object* v_buckets_x27_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
lean_inc(v_bkt_592_);
v___x_611_ = lean_box(0);
v_buckets_x27_612_ = lean_array_uset(v_buckets_575_, v___x_591_, v___x_611_);
v___x_613_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_572_, v_b_573_, v_bkt_592_);
v___x_614_ = lean_array_uset(v_buckets_x27_612_, v___x_591_, v___x_613_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_614_);
v___x_616_ = v___x_577_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_size_574_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_619_, lean_object* v_as_x27_620_, lean_object* v_b_621_){
_start:
{
if (lean_obj_tag(v_as_x27_620_) == 0)
{
lean_dec_ref(v_v_619_);
return v_b_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_624_; 
v_head_622_ = lean_ctor_get(v_as_x27_620_, 0);
v_tail_623_ = lean_ctor_get(v_as_x27_620_, 1);
lean_inc_ref(v_v_619_);
lean_inc(v_head_622_);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_621_, v_head_622_, v_v_619_);
v_as_x27_620_ = v_tail_623_;
v_b_621_ = v___x_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_626_, lean_object* v_as_x27_627_, lean_object* v_b_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_626_, v_as_x27_627_, v_b_628_);
lean_dec(v_as_x27_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_630_, lean_object* v_e_631_, lean_object* v_v_632_, lean_object* v_a_633_){
_start:
{
uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = 0;
v___x_635_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_630_, v_e_631_, v___x_634_);
v___x_636_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_632_, v___x_635_, v_a_633_);
lean_dec(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_637_, lean_object* v_e_638_, lean_object* v_v_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_637_, v_e_638_, v_v_639_, v_a_640_);
lean_dec_ref(v_goal_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_642_, lean_object* v_m_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_643_, v_a_644_, v_b_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_647_, lean_object* v_as_648_, lean_object* v_as_x27_649_, lean_object* v_b_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_647_, v_as_x27_649_, v_b_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_653_, lean_object* v_as_654_, lean_object* v_as_x27_655_, lean_object* v_b_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_653_, v_as_654_, v_as_x27_655_, v_b_656_, v_a_657_);
lean_dec(v_as_x27_655_);
lean_dec(v_as_654_);
return v_res_658_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_659_, lean_object* v_a_660_, lean_object* v_x_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_663_, lean_object* v_a_664_, lean_object* v_x_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_663_, v_a_664_, v_x_665_);
lean_dec(v_x_665_);
lean_dec_ref(v_a_664_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_668_, lean_object* v_data_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_671_, lean_object* v_a_672_, lean_object* v_b_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_672_, v_b_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_676_, lean_object* v_i_677_, lean_object* v_source_678_, lean_object* v_target_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_677_, v_source_678_, v_target_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
return v_x_685_;
}
else
{
lean_object* v_key_687_; lean_object* v_value_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_726_; 
v_key_687_ = lean_ctor_get(v_x_686_, 0);
v_value_688_ = lean_ctor_get(v_x_686_, 1);
v_tail_689_ = lean_ctor_get(v_x_686_, 2);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_726_ == 0)
{
v___x_691_ = v_x_686_;
v_isShared_692_ = v_isSharedCheck_726_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_value_688_);
lean_inc(v_key_687_);
lean_dec(v_x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_726_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint64_t v___y_695_; lean_object* v_intZero_713_; uint8_t v_isNeg_714_; 
v___x_693_ = lean_array_get_size(v_x_685_);
v_intZero_713_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_714_ = lean_int_dec_lt(v_key_687_, v_intZero_713_);
if (v_isNeg_714_ == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint64_t v___x_718_; 
v_a_715_ = lean_nat_abs(v_key_687_);
v___x_716_ = lean_unsigned_to_nat(2u);
v___x_717_ = lean_nat_mul(v___x_716_, v_a_715_);
lean_dec(v_a_715_);
v___x_718_ = lean_uint64_of_nat(v___x_717_);
lean_dec(v___x_717_);
v___y_695_ = v___x_718_;
goto v___jp_694_;
}
else
{
lean_object* v_abs_719_; lean_object* v_one_720_; lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint64_t v___x_725_; 
v_abs_719_ = lean_nat_abs(v_key_687_);
v_one_720_ = lean_unsigned_to_nat(1u);
v_a_721_ = lean_nat_sub(v_abs_719_, v_one_720_);
lean_dec(v_abs_719_);
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = lean_nat_mul(v___x_722_, v_a_721_);
lean_dec(v_a_721_);
v___x_724_ = lean_nat_add(v___x_723_, v_one_720_);
lean_dec(v___x_723_);
v___x_725_ = lean_uint64_of_nat(v___x_724_);
lean_dec(v___x_724_);
v___y_695_ = v___x_725_;
goto v___jp_694_;
}
v___jp_694_:
{
uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v_fold_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_696_ = 32ULL;
v___x_697_ = lean_uint64_shift_right(v___y_695_, v___x_696_);
v_fold_698_ = lean_uint64_xor(v___y_695_, v___x_697_);
v___x_699_ = 16ULL;
v___x_700_ = lean_uint64_shift_right(v_fold_698_, v___x_699_);
v___x_701_ = lean_uint64_xor(v_fold_698_, v___x_700_);
v___x_702_ = lean_uint64_to_usize(v___x_701_);
v___x_703_ = lean_usize_of_nat(v___x_693_);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_sub(v___x_703_, v___x_704_);
v___x_706_ = lean_usize_land(v___x_702_, v___x_705_);
v___x_707_ = lean_array_uget_borrowed(v_x_685_, v___x_706_);
lean_inc(v___x_707_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v___x_707_);
v___x_709_ = v___x_691_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_value_688_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v___x_707_);
v___x_709_ = v_reuseFailAlloc_712_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = lean_array_uset(v_x_685_, v___x_706_, v___x_709_);
v_x_685_ = v___x_710_;
v_x_686_ = v_tail_689_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_727_, lean_object* v_source_728_, lean_object* v_target_729_){
_start:
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_get_size(v_source_728_);
v___x_731_ = lean_nat_dec_lt(v_i_727_, v___x_730_);
if (v___x_731_ == 0)
{
lean_dec_ref(v_source_728_);
lean_dec(v_i_727_);
return v_target_729_;
}
else
{
lean_object* v_es_732_; lean_object* v___x_733_; lean_object* v_source_734_; lean_object* v_target_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_es_732_ = lean_array_fget(v_source_728_, v_i_727_);
v___x_733_ = lean_box(0);
v_source_734_ = lean_array_fset(v_source_728_, v_i_727_, v___x_733_);
v_target_735_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_729_, v_es_732_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_i_727_, v___x_736_);
lean_dec(v_i_727_);
v_i_727_ = v___x_737_;
v_source_728_ = v_source_734_;
v_target_729_ = v_target_735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_nbuckets_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_740_ = lean_array_get_size(v_data_739_);
v___x_741_ = lean_unsigned_to_nat(2u);
v_nbuckets_742_ = lean_nat_mul(v___x_740_, v___x_741_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_box(0);
v___x_745_ = lean_mk_array(v_nbuckets_742_, v___x_744_);
v___x_746_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_743_, v_data_739_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v_size_750_; lean_object* v_buckets_751_; lean_object* v___x_752_; uint64_t v___y_754_; lean_object* v_intZero_791_; uint8_t v_isNeg_792_; 
v_size_750_ = lean_ctor_get(v_m_747_, 0);
v_buckets_751_ = lean_ctor_get(v_m_747_, 1);
v___x_752_ = lean_array_get_size(v_buckets_751_);
v_intZero_791_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_792_ = lean_int_dec_lt(v_a_748_, v_intZero_791_);
if (v_isNeg_792_ == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint64_t v___x_796_; 
v_a_793_ = lean_nat_abs(v_a_748_);
v___x_794_ = lean_unsigned_to_nat(2u);
v___x_795_ = lean_nat_mul(v___x_794_, v_a_793_);
lean_dec(v_a_793_);
v___x_796_ = lean_uint64_of_nat(v___x_795_);
lean_dec(v___x_795_);
v___y_754_ = v___x_796_;
goto v___jp_753_;
}
else
{
lean_object* v_abs_797_; lean_object* v_one_798_; lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint64_t v___x_803_; 
v_abs_797_ = lean_nat_abs(v_a_748_);
v_one_798_ = lean_unsigned_to_nat(1u);
v_a_799_ = lean_nat_sub(v_abs_797_, v_one_798_);
lean_dec(v_abs_797_);
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = lean_nat_mul(v___x_800_, v_a_799_);
lean_dec(v_a_799_);
v___x_802_ = lean_nat_add(v___x_801_, v_one_798_);
lean_dec(v___x_801_);
v___x_803_ = lean_uint64_of_nat(v___x_802_);
lean_dec(v___x_802_);
v___y_754_ = v___x_803_;
goto v___jp_753_;
}
v___jp_753_:
{
uint64_t v___x_755_; uint64_t v___x_756_; uint64_t v_fold_757_; uint64_t v___x_758_; uint64_t v___x_759_; uint64_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v_bkt_766_; uint8_t v___x_767_; 
v___x_755_ = 32ULL;
v___x_756_ = lean_uint64_shift_right(v___y_754_, v___x_755_);
v_fold_757_ = lean_uint64_xor(v___y_754_, v___x_756_);
v___x_758_ = 16ULL;
v___x_759_ = lean_uint64_shift_right(v_fold_757_, v___x_758_);
v___x_760_ = lean_uint64_xor(v_fold_757_, v___x_759_);
v___x_761_ = lean_uint64_to_usize(v___x_760_);
v___x_762_ = lean_usize_of_nat(v___x_752_);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_sub(v___x_762_, v___x_763_);
v___x_765_ = lean_usize_land(v___x_761_, v___x_764_);
v_bkt_766_ = lean_array_uget_borrowed(v_buckets_751_, v___x_765_);
v___x_767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_748_, v_bkt_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_788_; 
lean_inc_ref(v_buckets_751_);
lean_inc(v_size_750_);
v_isSharedCheck_788_ = !lean_is_exclusive(v_m_747_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; 
v_unused_789_ = lean_ctor_get(v_m_747_, 1);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_m_747_, 0);
lean_dec(v_unused_790_);
v___x_769_ = v_m_747_;
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
else
{
lean_dec(v_m_747_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v_size_x27_772_; lean_object* v___x_773_; lean_object* v_buckets_x27_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v_size_x27_772_ = lean_nat_add(v_size_750_, v___x_771_);
lean_dec(v_size_750_);
lean_inc(v_bkt_766_);
v___x_773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_773_, 0, v_a_748_);
lean_ctor_set(v___x_773_, 1, v_b_749_);
lean_ctor_set(v___x_773_, 2, v_bkt_766_);
v_buckets_x27_774_ = lean_array_uset(v_buckets_751_, v___x_765_, v___x_773_);
v___x_775_ = lean_unsigned_to_nat(4u);
v___x_776_ = lean_nat_mul(v_size_x27_772_, v___x_775_);
v___x_777_ = lean_unsigned_to_nat(3u);
v___x_778_ = lean_nat_div(v___x_776_, v___x_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_array_get_size(v_buckets_x27_774_);
v___x_780_ = lean_nat_dec_le(v___x_778_, v___x_779_);
lean_dec(v___x_778_);
if (v___x_780_ == 0)
{
lean_object* v_val_781_; lean_object* v___x_783_; 
v_val_781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_774_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_val_781_);
lean_ctor_set(v___x_769_, 0, v_size_x27_772_);
v___x_783_ = v___x_769_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_size_x27_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_val_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v___x_786_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_buckets_x27_774_);
lean_ctor_set(v___x_769_, 0, v_size_x27_772_);
v___x_786_ = v___x_769_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_size_x27_772_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_buckets_x27_774_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_dec(v_b_749_);
lean_dec(v_a_748_);
return v_m_747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_804_, lean_object* v_isTarget_805_, lean_object* v_as_806_, size_t v_sz_807_, size_t v_i_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_808_, v_sz_807_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v_isTarget_805_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v_b_809_);
return v___x_816_;
}
else
{
lean_object* v_snd_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_899_; 
v_snd_817_ = lean_ctor_get(v_b_809_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_b_809_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_b_809_, 0);
lean_dec(v_unused_900_);
v___x_819_ = v_b_809_;
v_isShared_820_ = v_isSharedCheck_899_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_817_);
lean_dec(v_b_809_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_899_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_array_uget_borrowed(v_as_806_, v_i_808_);
lean_inc(v_a_821_);
v___x_822_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_804_, v_a_821_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_snd_823_; lean_object* v_a_824_; lean_object* v_fst_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_889_; 
v_snd_823_ = lean_ctor_get(v_snd_817_, 1);
lean_inc(v_snd_823_);
v_a_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_822_, 1);
v_fst_825_ = lean_ctor_get(v_snd_817_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_snd_817_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_snd_817_, 1);
lean_dec(v_unused_890_);
v___x_827_ = v_snd_817_;
v_isShared_828_ = v_isSharedCheck_889_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_fst_825_);
lean_dec(v_snd_817_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_889_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_888_; 
v_fst_829_ = lean_ctor_get(v_snd_823_, 0);
v_snd_830_ = lean_ctor_get(v_snd_823_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_snd_823_);
if (v_isSharedCheck_888_ == 0)
{
v___x_832_ = v_snd_823_;
v_isShared_833_ = v_isSharedCheck_888_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_inc(v_fst_829_);
lean_dec(v_snd_823_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_888_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_a_836_; uint8_t v___x_843_; 
v___x_834_ = lean_box(0);
v___x_843_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_824_);
if (v___x_843_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_a_824_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v_snd_830_);
lean_ctor_set(v___x_827_, 0, v_fst_829_);
v___x_845_ = v___x_827_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_snd_830_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_845_);
lean_ctor_set(v___x_819_, 0, v_fst_825_);
v___x_847_ = v___x_819_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_fst_825_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_836_ = v___x_847_;
goto v___jp_835_;
}
}
}
else
{
lean_object* v___x_850_; 
lean_inc_ref(v_isTarget_805_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v_a_824_);
v___x_850_ = lean_apply_6(v_isTarget_805_, v_a_824_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, lean_box(0));
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; uint8_t v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_unbox(v_a_851_);
lean_dec(v_a_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_a_824_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v_snd_830_);
lean_ctor_set(v___x_827_, 0, v_fst_829_);
v___x_854_ = v___x_827_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_snd_830_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_854_);
lean_ctor_set(v___x_819_, 0, v_fst_825_);
v___x_856_ = v___x_819_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_fst_825_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v_a_836_ = v___x_856_;
goto v___jp_835_;
}
}
}
else
{
lean_object* v_self_859_; lean_object* v___x_860_; 
v_self_859_ = lean_ctor_get(v_a_824_, 0);
lean_inc_ref(v_self_859_);
lean_dec(v_a_824_);
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_830_, v_self_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_804_, v_snd_830_, v_self_859_, v_fst_829_, v_fst_825_);
lean_inc_n(v___x_861_, 2);
v___x_862_ = l_Rat_ofInt(v___x_861_);
v___x_863_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_804_, v_self_859_, v___x_862_, v_snd_830_);
v___x_864_ = lean_box(0);
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_829_, v___x_861_, v___x_864_);
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_867_ = lean_int_add(v___x_861_, v___x_866_);
lean_dec(v___x_861_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___x_863_);
lean_ctor_set(v___x_827_, 0, v___x_865_);
v___x_869_ = v___x_827_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_863_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_869_);
lean_ctor_set(v___x_819_, 0, v___x_867_);
v___x_871_ = v___x_819_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_a_836_ = v___x_871_;
goto v___jp_835_;
}
}
}
else
{
lean_object* v___x_875_; 
lean_dec_ref_known(v___x_860_, 1);
lean_dec_ref(v_self_859_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v_snd_830_);
lean_ctor_set(v___x_827_, 0, v_fst_829_);
v___x_875_ = v___x_827_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_snd_830_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v___x_875_);
lean_ctor_set(v___x_819_, 0, v_fst_825_);
v___x_877_ = v___x_819_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_fst_825_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_836_ = v___x_877_;
goto v___jp_835_;
}
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_del_object(v___x_832_);
lean_dec(v_snd_830_);
lean_dec(v_fst_829_);
lean_del_object(v___x_827_);
lean_dec(v_fst_825_);
lean_dec(v_a_824_);
lean_del_object(v___x_819_);
lean_dec_ref(v_isTarget_805_);
v_a_880_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_850_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_850_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
v___jp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_a_836_);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_838_ = v___x_832_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_808_, v___x_839_);
v_i_808_ = v___x_840_;
v_b_809_ = v___x_838_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_819_);
lean_dec(v_snd_817_);
lean_dec_ref(v_isTarget_805_);
v_a_891_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_822_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_822_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_901_, lean_object* v_isTarget_902_, lean_object* v_as_903_, lean_object* v_sz_904_, lean_object* v_i_905_, lean_object* v_b_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_904_);
lean_dec(v_sz_904_);
v_i_boxed_913_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_901_, v_isTarget_902_, v_as_903_, v_sz_boxed_912_, v_i_boxed_913_, v_b_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_as_903_);
lean_dec_ref(v_goal_901_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_915_, lean_object* v_isTarget_916_, lean_object* v_as_917_, size_t v_sz_918_, size_t v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec_ref(v_isTarget_916_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_b_920_);
return v___x_927_;
}
else
{
lean_object* v_snd_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_1010_; 
v_snd_928_ = lean_ctor_get(v_b_920_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_b_920_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_b_920_, 0);
lean_dec(v_unused_1011_);
v___x_930_ = v_b_920_;
v_isShared_931_ = v_isSharedCheck_1010_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snd_928_);
lean_dec(v_b_920_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_1010_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_array_uget_borrowed(v_as_917_, v_i_919_);
lean_inc(v_a_932_);
v___x_933_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_915_, v_a_932_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_snd_934_; lean_object* v_a_935_; lean_object* v_fst_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1000_; 
v_snd_934_ = lean_ctor_get(v_snd_928_, 1);
lean_inc(v_snd_934_);
v_a_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_933_, 1);
v_fst_936_ = lean_ctor_get(v_snd_928_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_snd_928_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_snd_928_, 1);
lean_dec(v_unused_1001_);
v___x_938_ = v_snd_928_;
v_isShared_939_ = v_isSharedCheck_1000_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_fst_936_);
lean_dec(v_snd_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1000_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_fst_940_; lean_object* v_snd_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_999_; 
v_fst_940_ = lean_ctor_get(v_snd_934_, 0);
v_snd_941_ = lean_ctor_get(v_snd_934_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_snd_934_);
if (v_isSharedCheck_999_ == 0)
{
v___x_943_ = v_snd_934_;
v_isShared_944_ = v_isSharedCheck_999_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_940_);
lean_dec(v_snd_934_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_999_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v_a_947_; uint8_t v___x_954_; 
v___x_945_ = lean_box(0);
v___x_954_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_935_);
if (v___x_954_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_a_935_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_snd_941_);
lean_ctor_set(v___x_938_, 0, v_fst_940_);
v___x_956_ = v___x_938_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_941_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_956_);
lean_ctor_set(v___x_930_, 0, v_fst_936_);
v___x_958_ = v___x_930_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_a_947_ = v___x_958_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v___x_961_; 
lean_inc_ref(v_isTarget_916_);
lean_inc(v___y_924_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v_a_935_);
v___x_961_ = lean_apply_6(v_isTarget_916_, v_a_935_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; uint8_t v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = lean_unbox(v_a_962_);
lean_dec(v_a_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v_a_935_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_snd_941_);
lean_ctor_set(v___x_938_, 0, v_fst_940_);
v___x_965_ = v___x_938_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_941_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_965_);
lean_ctor_set(v___x_930_, 0, v_fst_936_);
v___x_967_ = v___x_930_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_947_ = v___x_967_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v_self_970_; lean_object* v___x_971_; 
v_self_970_ = lean_ctor_get(v_a_935_, 0);
lean_inc_ref(v_self_970_);
lean_dec(v_a_935_);
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_941_, v_self_970_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_972_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_915_, v_snd_941_, v_self_970_, v_fst_940_, v_fst_936_);
lean_inc_n(v___x_972_, 2);
v___x_973_ = l_Rat_ofInt(v___x_972_);
v___x_974_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_915_, v_self_970_, v___x_973_, v_snd_941_);
v___x_975_ = lean_box(0);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_940_, v___x_972_, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_978_ = lean_int_add(v___x_972_, v___x_977_);
lean_dec(v___x_972_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_974_);
lean_ctor_set(v___x_938_, 0, v___x_976_);
v___x_980_ = v___x_938_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_974_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_980_);
lean_ctor_set(v___x_930_, 0, v___x_978_);
v___x_982_ = v___x_930_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_947_ = v___x_982_;
goto v___jp_946_;
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec_ref_known(v___x_971_, 1);
lean_dec_ref(v_self_970_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_snd_941_);
lean_ctor_set(v___x_938_, 0, v_fst_940_);
v___x_986_ = v___x_938_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_940_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_snd_941_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_986_);
lean_ctor_set(v___x_930_, 0, v_fst_936_);
v___x_988_ = v___x_930_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v_a_947_ = v___x_988_;
goto v___jp_946_;
}
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_943_);
lean_dec(v_snd_941_);
lean_dec(v_fst_940_);
lean_del_object(v___x_938_);
lean_dec(v_fst_936_);
lean_dec(v_a_935_);
lean_del_object(v___x_930_);
lean_dec_ref(v_isTarget_916_);
v_a_991_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_961_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_961_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
v___jp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v_a_947_);
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_a_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_919_, v___x_950_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_915_, v_isTarget_916_, v_as_917_, v_sz_918_, v___x_951_, v___x_949_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_952_;
}
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_930_);
lean_dec(v_snd_928_);
lean_dec_ref(v_isTarget_916_);
v_a_1002_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_933_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_933_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1012_, lean_object* v_isTarget_1013_, lean_object* v_as_1014_, lean_object* v_sz_1015_, lean_object* v_i_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
size_t v_sz_boxed_1023_; size_t v_i_boxed_1024_; lean_object* v_res_1025_; 
v_sz_boxed_1023_ = lean_unbox_usize(v_sz_1015_);
lean_dec(v_sz_1015_);
v_i_boxed_1024_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1012_, v_isTarget_1013_, v_as_1014_, v_sz_boxed_1023_, v_i_boxed_1024_, v_b_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_as_1014_);
lean_dec_ref(v_goal_1012_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1026_, lean_object* v_isTarget_1027_, lean_object* v_as_1028_, size_t v_sz_1029_, size_t v_i_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_lt(v_i_1030_, v_sz_1029_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_isTarget_1027_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_b_1031_);
return v___x_1038_;
}
else
{
lean_object* v_snd_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1121_; 
v_snd_1039_ = lean_ctor_get(v_b_1031_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_b_1031_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_b_1031_, 0);
lean_dec(v_unused_1122_);
v___x_1041_ = v_b_1031_;
v_isShared_1042_ = v_isSharedCheck_1121_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_snd_1039_);
lean_dec(v_b_1031_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1121_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_a_1043_; lean_object* v___x_1044_; 
v_a_1043_ = lean_array_uget_borrowed(v_as_1028_, v_i_1030_);
lean_inc(v_a_1043_);
v___x_1044_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1026_, v_a_1043_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_snd_1045_; lean_object* v_a_1046_; lean_object* v_fst_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1111_; 
v_snd_1045_ = lean_ctor_get(v_snd_1039_, 1);
lean_inc(v_snd_1045_);
v_a_1046_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1044_, 1);
v_fst_1047_ = lean_ctor_get(v_snd_1039_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_snd_1039_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v_snd_1039_, 1);
lean_dec(v_unused_1112_);
v___x_1049_ = v_snd_1039_;
v_isShared_1050_ = v_isSharedCheck_1111_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_fst_1047_);
lean_dec(v_snd_1039_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1111_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1110_; 
v_fst_1051_ = lean_ctor_get(v_snd_1045_, 0);
v_snd_1052_ = lean_ctor_get(v_snd_1045_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_snd_1045_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1054_ = v_snd_1045_;
v_isShared_1055_ = v_isSharedCheck_1110_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v_snd_1045_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1110_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v_a_1058_; uint8_t v___x_1065_; 
v___x_1056_ = lean_box(0);
v___x_1065_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1046_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1067_; 
lean_dec(v_a_1046_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_snd_1052_);
lean_ctor_set(v___x_1049_, 0, v_fst_1051_);
v___x_1067_ = v___x_1049_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_snd_1052_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1069_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1067_);
lean_ctor_set(v___x_1041_, 0, v_fst_1047_);
v___x_1069_ = v___x_1041_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v_a_1058_ = v___x_1069_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v___x_1072_; 
lean_inc_ref(v_isTarget_1027_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc(v_a_1046_);
v___x_1072_ = lean_apply_6(v_isTarget_1027_, v_a_1046_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, lean_box(0));
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; uint8_t v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_unbox(v_a_1073_);
lean_dec(v_a_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_a_1046_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_snd_1052_);
lean_ctor_set(v___x_1049_, 0, v_fst_1051_);
v___x_1076_ = v___x_1049_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_snd_1052_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1076_);
lean_ctor_set(v___x_1041_, 0, v_fst_1047_);
v___x_1078_ = v___x_1041_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_a_1058_ = v___x_1078_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v_self_1081_; lean_object* v___x_1082_; 
v_self_1081_ = lean_ctor_get(v_a_1046_, 0);
lean_inc_ref(v_self_1081_);
lean_dec(v_a_1046_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1052_, v_self_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1083_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1026_, v_snd_1052_, v_self_1081_, v_fst_1051_, v_fst_1047_);
lean_inc_n(v___x_1083_, 2);
v___x_1084_ = l_Rat_ofInt(v___x_1083_);
v___x_1085_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1026_, v_self_1081_, v___x_1084_, v_snd_1052_);
v___x_1086_ = lean_box(0);
v___x_1087_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1051_, v___x_1083_, v___x_1086_);
v___x_1088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1089_ = lean_int_add(v___x_1083_, v___x_1088_);
lean_dec(v___x_1083_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1085_);
lean_ctor_set(v___x_1049_, 0, v___x_1087_);
v___x_1091_ = v___x_1049_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1085_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1091_);
lean_ctor_set(v___x_1041_, 0, v___x_1089_);
v___x_1093_ = v___x_1041_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_a_1058_ = v___x_1093_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v___x_1097_; 
lean_dec_ref_known(v___x_1082_, 1);
lean_dec_ref(v_self_1081_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_snd_1052_);
lean_ctor_set(v___x_1049_, 0, v_fst_1051_);
v___x_1097_ = v___x_1049_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_snd_1052_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1097_);
lean_ctor_set(v___x_1041_, 0, v_fst_1047_);
v___x_1099_ = v___x_1041_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
v_a_1058_ = v___x_1099_;
goto v___jp_1057_;
}
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_del_object(v___x_1054_);
lean_dec(v_snd_1052_);
lean_dec(v_fst_1051_);
lean_del_object(v___x_1049_);
lean_dec(v_fst_1047_);
lean_dec(v_a_1046_);
lean_del_object(v___x_1041_);
lean_dec_ref(v_isTarget_1027_);
v_a_1102_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1072_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1072_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_a_1058_);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1060_ = v___x_1054_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_a_1058_);
v___x_1060_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
size_t v___x_1061_; size_t v___x_1062_; 
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1030_, v___x_1061_);
v_i_1030_ = v___x_1062_;
v_b_1031_ = v___x_1060_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_del_object(v___x_1041_);
lean_dec(v_snd_1039_);
lean_dec_ref(v_isTarget_1027_);
v_a_1113_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1044_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1044_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1123_, lean_object* v_isTarget_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1123_, v_isTarget_1124_, v_as_1125_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec_ref(v_goal_1123_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1137_, lean_object* v_isTarget_1138_, lean_object* v_as_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_b_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref(v_isTarget_1138_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1142_);
return v___x_1149_;
}
else
{
lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1232_; 
v_snd_1150_ = lean_ctor_get(v_b_1142_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_b_1142_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_b_1142_, 0);
lean_dec(v_unused_1233_);
v___x_1152_ = v_b_1142_;
v_isShared_1153_ = v_isSharedCheck_1232_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_dec(v_b_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1232_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_array_uget_borrowed(v_as_1139_, v_i_1141_);
lean_inc(v_a_1154_);
v___x_1155_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1137_, v_a_1154_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_snd_1156_; lean_object* v_a_1157_; lean_object* v_fst_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1222_; 
v_snd_1156_ = lean_ctor_get(v_snd_1150_, 1);
lean_inc(v_snd_1156_);
v_a_1157_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1155_, 1);
v_fst_1158_ = lean_ctor_get(v_snd_1150_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_snd_1150_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_snd_1150_, 1);
lean_dec(v_unused_1223_);
v___x_1160_ = v_snd_1150_;
v_isShared_1161_ = v_isSharedCheck_1222_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_fst_1158_);
lean_dec(v_snd_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1222_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1221_; 
v_fst_1162_ = lean_ctor_get(v_snd_1156_, 0);
v_snd_1163_ = lean_ctor_get(v_snd_1156_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_snd_1156_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1165_ = v_snd_1156_;
v_isShared_1166_ = v_isSharedCheck_1221_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snd_1163_);
lean_inc(v_fst_1162_);
lean_dec(v_snd_1156_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1221_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v_a_1169_; uint8_t v___x_1176_; 
v___x_1167_ = lean_box(0);
v___x_1176_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1157_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1178_; 
lean_dec(v_a_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v_snd_1163_);
lean_ctor_set(v___x_1160_, 0, v_fst_1162_);
v___x_1178_ = v___x_1160_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_fst_1162_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_snd_1163_);
v___x_1178_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1178_);
lean_ctor_set(v___x_1152_, 0, v_fst_1158_);
v___x_1180_ = v___x_1152_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_fst_1158_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v_a_1169_ = v___x_1180_;
goto v___jp_1168_;
}
}
}
else
{
lean_object* v___x_1183_; 
lean_inc_ref(v_isTarget_1138_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v_a_1157_);
v___x_1183_ = lean_apply_6(v_isTarget_1138_, v_a_1157_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, lean_box(0));
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; uint8_t v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = lean_unbox(v_a_1184_);
lean_dec(v_a_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_dec(v_a_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v_snd_1163_);
lean_ctor_set(v___x_1160_, 0, v_fst_1162_);
v___x_1187_ = v___x_1160_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1162_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1163_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1187_);
lean_ctor_set(v___x_1152_, 0, v_fst_1158_);
v___x_1189_ = v___x_1152_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_fst_1158_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_a_1169_ = v___x_1189_;
goto v___jp_1168_;
}
}
}
else
{
lean_object* v_self_1192_; lean_object* v___x_1193_; 
v_self_1192_ = lean_ctor_get(v_a_1157_, 0);
lean_inc_ref(v_self_1192_);
lean_dec(v_a_1157_);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1163_, v_self_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1194_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1137_, v_snd_1163_, v_self_1192_, v_fst_1162_, v_fst_1158_);
lean_inc_n(v___x_1194_, 2);
v___x_1195_ = l_Rat_ofInt(v___x_1194_);
v___x_1196_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1137_, v_self_1192_, v___x_1195_, v_snd_1163_);
v___x_1197_ = lean_box(0);
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1162_, v___x_1194_, v___x_1197_);
v___x_1199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1200_ = lean_int_add(v___x_1194_, v___x_1199_);
lean_dec(v___x_1194_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1196_);
lean_ctor_set(v___x_1160_, 0, v___x_1198_);
v___x_1202_ = v___x_1160_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1196_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1202_);
lean_ctor_set(v___x_1152_, 0, v___x_1200_);
v___x_1204_ = v___x_1152_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v_a_1169_ = v___x_1204_;
goto v___jp_1168_;
}
}
}
else
{
lean_object* v___x_1208_; 
lean_dec_ref_known(v___x_1193_, 1);
lean_dec_ref(v_self_1192_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v_snd_1163_);
lean_ctor_set(v___x_1160_, 0, v_fst_1162_);
v___x_1208_ = v___x_1160_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_fst_1162_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_snd_1163_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___x_1208_);
lean_ctor_set(v___x_1152_, 0, v_fst_1158_);
v___x_1210_ = v___x_1152_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_fst_1158_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v_a_1169_ = v___x_1210_;
goto v___jp_1168_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1165_);
lean_dec(v_snd_1163_);
lean_dec(v_fst_1162_);
lean_del_object(v___x_1160_);
lean_dec(v_fst_1158_);
lean_dec(v_a_1157_);
lean_del_object(v___x_1152_);
lean_dec_ref(v_isTarget_1138_);
v_a_1213_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1183_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1183_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v_a_1169_);
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1171_ = v___x_1165_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_a_1169_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_add(v_i_1141_, v___x_1172_);
v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1137_, v_isTarget_1138_, v_as_1139_, v_sz_1140_, v___x_1173_, v___x_1171_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1174_;
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_del_object(v___x_1152_);
lean_dec(v_snd_1150_);
lean_dec_ref(v_isTarget_1138_);
v_a_1224_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1155_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1155_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1234_, lean_object* v_isTarget_1235_, lean_object* v_as_1236_, lean_object* v_sz_1237_, lean_object* v_i_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1237_);
lean_dec(v_sz_1237_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1238_);
lean_dec(v_i_1238_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1234_, v_isTarget_1235_, v_as_1236_, v_sz_boxed_1245_, v_i_boxed_1246_, v_b_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec_ref(v_as_1236_);
lean_dec_ref(v_goal_1234_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1248_, lean_object* v_goal_1249_, lean_object* v_isTarget_1250_, lean_object* v_n_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
if (lean_obj_tag(v_n_1251_) == 0)
{
lean_object* v_cs_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; size_t v_sz_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_cs_1258_ = lean_ctor_get(v_n_1251_, 0);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_b_1252_);
v_sz_1261_ = lean_array_size(v_cs_1258_);
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1248_, v_goal_1249_, v_isTarget_1250_, v_cs_1258_, v_sz_1261_, v___x_1262_, v___x_1260_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_fst_1268_; 
v_fst_1268_ = lean_ctor_get(v_a_1264_, 0);
if (lean_obj_tag(v_fst_1268_) == 0)
{
lean_object* v_snd_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v_snd_1269_ = lean_ctor_get(v_a_1264_, 1);
lean_inc(v_snd_1269_);
lean_dec(v_a_1264_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_snd_1269_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1270_);
v___x_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v_val_1274_; lean_object* v___x_1276_; 
lean_inc_ref(v_fst_1268_);
lean_dec(v_a_1264_);
v_val_1274_ = lean_ctor_get(v_fst_1268_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v_fst_1268_, 1);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_val_1274_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_val_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
v_a_1279_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1263_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1263_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_vs_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; size_t v_sz_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v_vs_1287_ = lean_ctor_get(v_n_1251_, 0);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_b_1252_);
v_sz_1290_ = lean_array_size(v_vs_1287_);
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1249_, v_isTarget_1250_, v_vs_1287_, v_sz_1290_, v___x_1291_, v___x_1289_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1307_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1307_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1307_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_fst_1297_; 
v_fst_1297_ = lean_ctor_get(v_a_1293_, 0);
if (lean_obj_tag(v_fst_1297_) == 0)
{
lean_object* v_snd_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v_snd_1298_ = lean_ctor_get(v_a_1293_, 1);
lean_inc(v_snd_1298_);
lean_dec(v_a_1293_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v_snd_1298_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1299_);
v___x_1301_ = v___x_1295_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1305_; 
lean_inc_ref(v_fst_1297_);
lean_dec(v_a_1293_);
v_val_1303_ = lean_ctor_get(v_fst_1297_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_fst_1297_, 1);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v_val_1303_);
v___x_1305_ = v___x_1295_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_a_1308_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1292_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1292_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1316_, lean_object* v_goal_1317_, lean_object* v_isTarget_1318_, lean_object* v_as_1319_, size_t v_sz_1320_, size_t v_i_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_usize_dec_lt(v_i_1321_, v_sz_1320_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref(v_isTarget_1318_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_b_1322_);
return v___x_1329_;
}
else
{
lean_object* v_snd_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1364_; 
v_snd_1330_ = lean_ctor_get(v_b_1322_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_b_1322_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_b_1322_, 0);
lean_dec(v_unused_1365_);
v___x_1332_ = v_b_1322_;
v_isShared_1333_ = v_isSharedCheck_1364_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_snd_1330_);
lean_dec(v_b_1322_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1364_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1334_ = lean_array_uget_borrowed(v_as_1319_, v_i_1321_);
lean_inc(v_snd_1330_);
lean_inc_ref(v_isTarget_1318_);
v___x_1335_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1316_, v_goal_1317_, v_isTarget_1318_, v_a_1334_, v_snd_1330_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1355_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1355_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1355_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
if (lean_obj_tag(v_a_1336_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec_ref(v_isTarget_1318_);
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_a_1336_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1340_);
v___x_1342_ = v___x_1332_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_snd_1330_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1342_);
v___x_1344_ = v___x_1338_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_del_object(v___x_1338_);
lean_dec(v_snd_1330_);
v_a_1347_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v_a_1336_, 1);
v___x_1348_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v_a_1347_);
lean_ctor_set(v___x_1332_, 0, v___x_1348_);
v___x_1350_ = v___x_1332_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_a_1347_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
size_t v___x_1351_; size_t v___x_1352_; 
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_add(v_i_1321_, v___x_1351_);
v_i_1321_ = v___x_1352_;
v_b_1322_ = v___x_1350_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_del_object(v___x_1332_);
lean_dec(v_snd_1330_);
lean_dec_ref(v_isTarget_1318_);
v_a_1356_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1335_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1335_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1366_, lean_object* v_goal_1367_, lean_object* v_isTarget_1368_, lean_object* v_as_1369_, lean_object* v_sz_1370_, lean_object* v_i_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
size_t v_sz_boxed_1378_; size_t v_i_boxed_1379_; lean_object* v_res_1380_; 
v_sz_boxed_1378_ = lean_unbox_usize(v_sz_1370_);
lean_dec(v_sz_1370_);
v_i_boxed_1379_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1366_, v_goal_1367_, v_isTarget_1368_, v_as_1369_, v_sz_boxed_1378_, v_i_boxed_1379_, v_b_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v_as_1369_);
lean_dec_ref(v_goal_1367_);
lean_dec_ref(v_init_1366_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1381_, lean_object* v_goal_1382_, lean_object* v_isTarget_1383_, lean_object* v_n_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1381_, v_goal_1382_, v_isTarget_1383_, v_n_1384_, v_b_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec_ref(v_n_1384_);
lean_dec_ref(v_goal_1382_);
lean_dec_ref(v_init_1381_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1392_, lean_object* v_isTarget_1393_, lean_object* v_t_1394_, lean_object* v_init_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_root_1401_; lean_object* v_tail_1402_; lean_object* v___x_1403_; 
v_root_1401_ = lean_ctor_get(v_t_1394_, 0);
v_tail_1402_ = lean_ctor_get(v_t_1394_, 1);
lean_inc_ref(v_isTarget_1393_);
lean_inc_ref(v_init_1395_);
v___x_1403_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1395_, v_goal_1392_, v_isTarget_1393_, v_root_1401_, v_init_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec_ref(v_init_1395_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1440_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1440_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1440_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
if (lean_obj_tag(v_a_1404_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_isTarget_1393_);
v_a_1408_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v_a_1404_, 1);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_a_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v_sz_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1406_);
v_a_1412_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v_a_1404_, 1);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1412_);
v_sz_1415_ = lean_array_size(v_tail_1402_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1392_, v_isTarget_1393_, v_tail_1402_, v_sz_1415_, v___x_1416_, v___x_1414_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1431_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1431_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1431_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_fst_1422_; 
v_fst_1422_ = lean_ctor_get(v_a_1418_, 0);
if (lean_obj_tag(v_fst_1422_) == 0)
{
lean_object* v_snd_1423_; lean_object* v___x_1425_; 
v_snd_1423_ = lean_ctor_get(v_a_1418_, 1);
lean_inc(v_snd_1423_);
lean_dec(v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v_snd_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_snd_1423_);
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
lean_object* v_val_1427_; lean_object* v___x_1429_; 
lean_inc_ref(v_fst_1422_);
lean_dec(v_a_1418_);
v_val_1427_ = lean_ctor_get(v_fst_1422_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v_fst_1422_, 1);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v_val_1427_);
v___x_1429_ = v___x_1420_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_val_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1417_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1417_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_isTarget_1393_);
v_a_1441_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1403_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1403_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1449_, lean_object* v_isTarget_1450_, lean_object* v_t_1451_, lean_object* v_init_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1449_, v_isTarget_1450_, v_t_1451_, v_init_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_t_1451_);
lean_dec_ref(v_goal_1449_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
if (lean_obj_tag(v_a_1459_) == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1460_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
else
{
lean_object* v_value_1464_; lean_object* v_tail_1465_; lean_object* v_num_1466_; lean_object* v_den_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_value_1464_ = lean_ctor_get(v_a_1459_, 1);
lean_inc(v_value_1464_);
v_tail_1465_ = lean_ctor_get(v_a_1459_, 2);
lean_inc(v_tail_1465_);
lean_dec_ref_known(v_a_1459_, 3);
v_num_1466_ = lean_ctor_get(v_value_1464_, 0);
lean_inc(v_num_1466_);
v_den_1467_ = lean_ctor_get(v_value_1464_, 1);
lean_inc(v_den_1467_);
lean_dec(v_value_1464_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_dec_eq(v_den_1467_, v___x_1468_);
lean_dec(v_den_1467_);
if (v___x_1469_ == 0)
{
lean_dec(v_num_1466_);
v_a_1459_ = v_tail_1465_;
goto _start;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1460_, v_num_1466_, v___x_1471_);
v_a_1459_ = v_tail_1465_;
v_a_1460_ = v___x_1472_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1474_, v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1478_, size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_usize_dec_lt(v_i_1480_, v_sz_1479_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_b_1481_);
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1489_ = lean_array_uget_borrowed(v_as_1478_, v_i_1480_);
lean_inc(v_a_1489_);
v___x_1490_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1489_, v_b_1481_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1503_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1503_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1503_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
if (lean_obj_tag(v_a_1491_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; 
v_a_1495_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v_a_1491_, 1);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v_a_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
else
{
lean_object* v_a_1499_; size_t v___x_1500_; size_t v___x_1501_; 
lean_del_object(v___x_1493_);
v_a_1499_ = lean_ctor_get(v_a_1491_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_a_1491_, 1);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_add(v_i_1480_, v___x_1500_);
v_i_1480_ = v___x_1501_;
v_b_1481_ = v_a_1499_;
goto _start;
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1490_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1490_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1512_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec_ref(v_as_1512_);
return v_res_1523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_unsigned_to_nat(16u);
v___x_1526_ = lean_mk_array(v___x_1525_, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_used_1529_; 
v___x_1527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1528_ = lean_unsigned_to_nat(0u);
v_used_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1529_, 0, v___x_1528_);
lean_ctor_set(v_used_1529_, 1, v___x_1527_);
return v_used_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1530_, lean_object* v_isTarget_1531_, lean_object* v_model_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v_buckets_1538_; lean_object* v_used_1539_; size_t v_sz_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v_buckets_1538_ = lean_ctor_get(v_model_1532_, 1);
v_used_1539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1540_ = lean_array_size(v_buckets_1538_);
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1538_, v_sz_1540_, v___x_1541_, v_used_1539_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_toGoalState_1543_; lean_object* v_a_1544_; lean_object* v_exprs_1545_; lean_object* v_nextVal_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_toGoalState_1543_ = lean_ctor_get(v_goal_1530_, 0);
v_a_1544_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1542_, 1);
v_exprs_1545_ = lean_ctor_get(v_toGoalState_1543_, 2);
v_nextVal_1546_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1544_);
lean_ctor_set(v___x_1547_, 1, v_model_1532_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_nextVal_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1530_, v_isTarget_1531_, v_exprs_1545_, v___x_1548_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1559_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_snd_1554_; lean_object* v_snd_1555_; lean_object* v___x_1557_; 
v_snd_1554_ = lean_ctor_get(v_a_1550_, 1);
lean_inc(v_snd_1554_);
lean_dec(v_a_1550_);
v_snd_1555_ = lean_ctor_get(v_snd_1554_, 1);
lean_inc(v_snd_1555_);
lean_dec(v_snd_1554_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_snd_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_snd_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1549_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1549_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_model_1532_);
lean_dec_ref(v_isTarget_1531_);
v_a_1568_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1542_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1542_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1576_, lean_object* v_isTarget_1577_, lean_object* v_model_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1576_, v_isTarget_1577_, v_model_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec_ref(v_goal_1576_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1585_, lean_object* v_m_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1586_, v_a_1587_, v_b_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1590_, v_a_1591_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1598_, v_a_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1606_, lean_object* v_data_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1609_, lean_object* v_i_1610_, lean_object* v_source_1611_, lean_object* v_target_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1610_, v_source_1611_, v_target_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1618_, lean_object* v_hi_1619_, lean_object* v_pivot_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_k_1623_){
_start:
{
uint8_t v___y_1625_; uint8_t v___x_1634_; 
v___x_1634_ = lean_nat_dec_lt(v_k_1623_, v_hi_1619_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_k_1623_);
v___x_1635_ = lean_array_fswap(v_as_1621_, v_i_1622_, v_hi_1619_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_i_1622_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; lean_object* v_fst_1638_; lean_object* v_fst_1639_; lean_object* v_g_u2081_1640_; lean_object* v_g_u2082_1641_; uint8_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1637_ = lean_array_fget_borrowed(v_as_1621_, v_k_1623_);
v_fst_1638_ = lean_ctor_get(v___x_1637_, 0);
v_fst_1639_ = lean_ctor_get(v_pivot_1620_, 0);
v_g_u2081_1640_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1618_, v_fst_1638_);
v_g_u2082_1641_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1618_, v_fst_1639_);
v___x_1642_ = lean_nat_dec_eq(v_g_u2081_1640_, v_g_u2082_1641_);
v___x_1643_ = lean_bool_not(v___x_1642_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; 
lean_dec(v_g_u2082_1641_);
lean_dec(v_g_u2081_1640_);
v___x_1644_ = lean_expr_lt(v_fst_1638_, v_fst_1639_);
v___y_1625_ = v___x_1644_;
goto v___jp_1624_;
}
else
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_lt(v_g_u2081_1640_, v_g_u2082_1641_);
lean_dec(v_g_u2082_1641_);
lean_dec(v_g_u2081_1640_);
v___y_1625_ = v___x_1645_;
goto v___jp_1624_;
}
}
v___jp_1624_:
{
if (v___y_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v_k_1623_, v___x_1626_);
lean_dec(v_k_1623_);
v_k_1623_ = v___x_1627_;
goto _start;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1629_ = lean_array_fswap(v_as_1621_, v_i_1622_, v_k_1623_);
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_add(v_i_1622_, v___x_1630_);
lean_dec(v_i_1622_);
v___x_1632_ = lean_nat_add(v_k_1623_, v___x_1630_);
lean_dec(v_k_1623_);
v_as_1621_ = v___x_1629_;
v_i_1622_ = v___x_1631_;
v_k_1623_ = v___x_1632_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1646_, lean_object* v_hi_1647_, lean_object* v_pivot_1648_, lean_object* v_as_1649_, lean_object* v_i_1650_, lean_object* v_k_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1646_, v_hi_1647_, v_pivot_1648_, v_as_1649_, v_i_1650_, v_k_1651_);
lean_dec_ref(v_pivot_1648_);
lean_dec(v_hi_1647_);
lean_dec_ref(v_goal_1646_);
return v_res_1652_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
lean_object* v_fst_1656_; lean_object* v_fst_1657_; lean_object* v_g_u2081_1658_; lean_object* v_g_u2082_1659_; uint8_t v___x_1660_; uint8_t v___x_1661_; 
v_fst_1656_ = lean_ctor_get(v_x_1654_, 0);
v_fst_1657_ = lean_ctor_get(v_x_1655_, 0);
v_g_u2081_1658_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1653_, v_fst_1656_);
v_g_u2082_1659_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1653_, v_fst_1657_);
v___x_1660_ = lean_nat_dec_eq(v_g_u2081_1658_, v_g_u2082_1659_);
v___x_1661_ = lean_bool_not(v___x_1660_);
if (v___x_1661_ == 0)
{
uint8_t v___x_1662_; 
lean_dec(v_g_u2082_1659_);
lean_dec(v_g_u2081_1658_);
v___x_1662_ = lean_expr_lt(v_fst_1656_, v_fst_1657_);
return v___x_1662_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_nat_dec_lt(v_g_u2081_1658_, v_g_u2082_1659_);
lean_dec(v_g_u2082_1659_);
lean_dec(v_g_u2081_1658_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1664_, v_x_1665_, v_x_1666_);
lean_dec_ref(v_x_1666_);
lean_dec_ref(v_x_1665_);
lean_dec_ref(v_goal_1664_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1669_, lean_object* v_n_1670_, lean_object* v_as_1671_, lean_object* v_lo_1672_, lean_object* v_hi_1673_){
_start:
{
lean_object* v___y_1675_; uint8_t v___x_1685_; 
v___x_1685_ = lean_nat_dec_lt(v_lo_1672_, v_hi_1673_);
if (v___x_1685_ == 0)
{
lean_dec(v_lo_1672_);
return v_as_1671_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_mid_1688_; lean_object* v___y_1690_; lean_object* v___y_1696_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1686_ = lean_nat_add(v_lo_1672_, v_hi_1673_);
v___x_1687_ = lean_unsigned_to_nat(1u);
v_mid_1688_ = lean_nat_shiftr(v___x_1686_, v___x_1687_);
lean_dec(v___x_1686_);
v___x_1701_ = lean_array_fget_borrowed(v_as_1671_, v_mid_1688_);
v___x_1702_ = lean_array_fget_borrowed(v_as_1671_, v_lo_1672_);
v___x_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1669_, v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1696_ = v_as_1671_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_array_fswap(v_as_1671_, v_lo_1672_, v_mid_1688_);
v___y_1696_ = v___x_1704_;
goto v___jp_1695_;
}
v___jp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = lean_array_fget_borrowed(v___y_1690_, v_mid_1688_);
v___x_1692_ = lean_array_fget_borrowed(v___y_1690_, v_hi_1673_);
v___x_1693_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1669_, v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_dec(v_mid_1688_);
v___y_1675_ = v___y_1690_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_array_fswap(v___y_1690_, v_mid_1688_, v_hi_1673_);
lean_dec(v_mid_1688_);
v___y_1675_ = v___x_1694_;
goto v___jp_1674_;
}
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = lean_array_fget_borrowed(v___y_1696_, v_hi_1673_);
v___x_1698_ = lean_array_fget_borrowed(v___y_1696_, v_lo_1672_);
v___x_1699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1669_, v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
v___y_1690_ = v___y_1696_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_array_fswap(v___y_1696_, v_lo_1672_, v_hi_1673_);
v___y_1690_ = v___x_1700_;
goto v___jp_1689_;
}
}
}
v___jp_1674_:
{
lean_object* v_pivot_1676_; lean_object* v___x_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; uint8_t v___x_1680_; 
v_pivot_1676_ = lean_array_fget(v___y_1675_, v_hi_1673_);
lean_inc_n(v_lo_1672_, 2);
v___x_1677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1669_, v_hi_1673_, v_pivot_1676_, v___y_1675_, v_lo_1672_, v_lo_1672_);
lean_dec(v_pivot_1676_);
v_fst_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_fst_1678_);
v_snd_1679_ = lean_ctor_get(v___x_1677_, 1);
lean_inc(v_snd_1679_);
lean_dec_ref(v___x_1677_);
v___x_1680_ = lean_nat_dec_le(v_hi_1673_, v_fst_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1669_, v_n_1670_, v_snd_1679_, v_lo_1672_, v_fst_1678_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v_fst_1678_, v___x_1682_);
lean_dec(v_fst_1678_);
v_as_1671_ = v___x_1681_;
v_lo_1672_ = v___x_1683_;
goto _start;
}
else
{
lean_dec(v_fst_1678_);
lean_dec(v_lo_1672_);
return v_snd_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1705_, lean_object* v_n_1706_, lean_object* v_as_1707_, lean_object* v_lo_1708_, lean_object* v_hi_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1705_, v_n_1706_, v_as_1707_, v_lo_1708_, v_hi_1709_);
lean_dec(v_hi_1709_);
lean_dec(v_n_1706_);
lean_dec_ref(v_goal_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1711_, lean_object* v_m_1712_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1713_ = lean_array_get_size(v_m_1712_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_nat_dec_eq(v___x_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___y_1719_; uint8_t v___x_1723_; 
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_sub(v___x_1713_, v___x_1716_);
v___x_1723_ = lean_nat_dec_le(v___x_1714_, v___x_1717_);
if (v___x_1723_ == 0)
{
lean_inc(v___x_1717_);
v___y_1719_ = v___x_1717_;
goto v___jp_1718_;
}
else
{
v___y_1719_ = v___x_1714_;
goto v___jp_1718_;
}
v___jp_1718_:
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_nat_dec_le(v___y_1719_, v___x_1717_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; 
lean_dec(v___x_1717_);
lean_inc(v___y_1719_);
v___x_1721_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1711_, v___x_1713_, v_m_1712_, v___y_1719_, v___y_1719_);
lean_dec(v___y_1719_);
return v___x_1721_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1711_, v___x_1713_, v_m_1712_, v___y_1719_, v___x_1717_);
lean_dec(v___x_1717_);
return v___x_1722_;
}
}
}
else
{
return v_m_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1724_, lean_object* v_m_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1724_, v_m_1725_);
lean_dec_ref(v_goal_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1727_, lean_object* v_n_1728_, lean_object* v_as_1729_, lean_object* v_lo_1730_, lean_object* v_hi_1731_, lean_object* v_w_1732_, lean_object* v_hlo_1733_, lean_object* v_hhi_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1727_, v_n_1728_, v_as_1729_, v_lo_1730_, v_hi_1731_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1736_, lean_object* v_n_1737_, lean_object* v_as_1738_, lean_object* v_lo_1739_, lean_object* v_hi_1740_, lean_object* v_w_1741_, lean_object* v_hlo_1742_, lean_object* v_hhi_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1736_, v_n_1737_, v_as_1738_, v_lo_1739_, v_hi_1740_, v_w_1741_, v_hlo_1742_, v_hhi_1743_);
lean_dec(v_hi_1740_);
lean_dec(v_n_1737_);
lean_dec_ref(v_goal_1736_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1745_, lean_object* v_n_1746_, lean_object* v_lo_1747_, lean_object* v_hi_1748_, lean_object* v_hhi_1749_, lean_object* v_pivot_1750_, lean_object* v_as_1751_, lean_object* v_i_1752_, lean_object* v_k_1753_, lean_object* v_ilo_1754_, lean_object* v_ik_1755_, lean_object* v_w_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1745_, v_hi_1748_, v_pivot_1750_, v_as_1751_, v_i_1752_, v_k_1753_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1758_, lean_object* v_n_1759_, lean_object* v_lo_1760_, lean_object* v_hi_1761_, lean_object* v_hhi_1762_, lean_object* v_pivot_1763_, lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_k_1766_, lean_object* v_ilo_1767_, lean_object* v_ik_1768_, lean_object* v_w_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1758_, v_n_1759_, v_lo_1760_, v_hi_1761_, v_hhi_1762_, v_pivot_1763_, v_as_1764_, v_i_1765_, v_k_1766_, v_ilo_1767_, v_ik_1768_, v_w_1769_);
lean_dec_ref(v_pivot_1763_);
lean_dec(v_hi_1761_);
lean_dec(v_lo_1760_);
lean_dec(v_n_1759_);
lean_dec_ref(v_goal_1758_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
if (lean_obj_tag(v_a_1771_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_a_1772_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v_key_1776_; lean_object* v_value_1777_; lean_object* v_tail_1778_; uint8_t v___x_1779_; 
v_key_1776_ = lean_ctor_get(v_a_1771_, 0);
lean_inc_n(v_key_1776_, 2);
v_value_1777_ = lean_ctor_get(v_a_1771_, 1);
lean_inc(v_value_1777_);
v_tail_1778_ = lean_ctor_get(v_a_1771_, 2);
lean_inc(v_tail_1778_);
lean_dec_ref_known(v_a_1771_, 3);
v___x_1779_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1776_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_key_1776_);
lean_ctor_set(v___x_1780_, 1, v_value_1777_);
v___x_1781_ = lean_array_push(v_a_1772_, v___x_1780_);
v_a_1771_ = v_tail_1778_;
v_a_1772_ = v___x_1781_;
goto _start;
}
else
{
lean_dec(v_value_1777_);
lean_dec(v_key_1776_);
v_a_1771_ = v_tail_1778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1784_, v_a_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1788_, size_t v_sz_1789_, size_t v_i_1790_, lean_object* v_b_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1790_, v_sz_1789_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_b_1791_);
return v___x_1798_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_array_uget_borrowed(v_as_1788_, v_i_1790_);
lean_inc(v_a_1799_);
v___x_1800_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1799_, v_b_1791_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1813_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1813_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; 
v_a_1805_ = lean_ctor_get(v_a_1801_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v_a_1801_, 1);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v_a_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
else
{
lean_object* v_a_1809_; size_t v___x_1810_; size_t v___x_1811_; 
lean_del_object(v___x_1803_);
v_a_1809_ = lean_ctor_get(v_a_1801_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v_a_1801_, 1);
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = lean_usize_add(v_i_1790_, v___x_1810_);
v_i_1790_ = v___x_1811_;
v_b_1791_ = v_a_1809_;
goto _start;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1800_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1800_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1822_, lean_object* v_sz_1823_, lean_object* v_i_1824_, lean_object* v_b_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
size_t v_sz_boxed_1831_; size_t v_i_boxed_1832_; lean_object* v_res_1833_; 
v_sz_boxed_1831_ = lean_unbox_usize(v_sz_1823_);
lean_dec(v_sz_1823_);
v_i_boxed_1832_ = lean_unbox_usize(v_i_1824_);
lean_dec(v_i_1824_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1822_, v_sz_boxed_1831_, v_i_boxed_1832_, v_b_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v_as_1822_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1836_, lean_object* v_isTarget_1837_, lean_object* v_model_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1836_, v_isTarget_1837_, v_model_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v_buckets_1846_; lean_object* v___x_1847_; size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_buckets_1846_ = lean_ctor_get(v_a_1845_, 1);
lean_inc_ref(v_buckets_1846_);
lean_dec(v_a_1845_);
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1848_ = lean_array_size(v_buckets_1846_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1846_, v_sz_1848_, v___x_1849_, v___x_1847_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec_ref(v_buckets_1846_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1836_, v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
return v___x_1850_;
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1844_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1844_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1868_, lean_object* v_isTarget_1869_, lean_object* v_model_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1868_, v_isTarget_1869_, v_model_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec_ref(v_goal_1868_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1877_, v_a_1878_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1885_, v_a_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v_env_1900_; lean_object* v___x_1901_; lean_object* v_mctx_1902_; lean_object* v_lctx_1903_; lean_object* v_options_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1899_ = lean_st_ref_get(v___y_1897_);
v_env_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc_ref(v_env_1900_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_st_ref_get(v___y_1895_);
v_mctx_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc_ref(v_mctx_1902_);
lean_dec(v___x_1901_);
v_lctx_1903_ = lean_ctor_get(v___y_1894_, 2);
v_options_1904_ = lean_ctor_get(v___y_1896_, 2);
lean_inc_ref(v_options_1904_);
lean_inc_ref(v_lctx_1903_);
v___x_1905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1905_, 0, v_env_1900_);
lean_ctor_set(v___x_1905_, 1, v_mctx_1902_);
lean_ctor_set(v___x_1905_, 2, v_lctx_1903_);
lean_ctor_set(v___x_1905_, 3, v_options_1904_);
v___x_1906_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_msgData_1893_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1914_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1915_; double v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_float_of_nat(v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1920_, lean_object* v_msg_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_ref_1927_; lean_object* v___x_1928_; lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1973_; 
v_ref_1927_ = lean_ctor_get(v___y_1924_, 5);
v___x_1928_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1973_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1973_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v_traceState_1934_; lean_object* v_env_1935_; lean_object* v_nextMacroScope_1936_; lean_object* v_ngen_1937_; lean_object* v_auxDeclNGen_1938_; lean_object* v_cache_1939_; lean_object* v_messages_1940_; lean_object* v_infoState_1941_; lean_object* v_snapshotTasks_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1972_; 
v___x_1933_ = lean_st_ref_take(v___y_1925_);
v_traceState_1934_ = lean_ctor_get(v___x_1933_, 4);
v_env_1935_ = lean_ctor_get(v___x_1933_, 0);
v_nextMacroScope_1936_ = lean_ctor_get(v___x_1933_, 1);
v_ngen_1937_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1938_ = lean_ctor_get(v___x_1933_, 3);
v_cache_1939_ = lean_ctor_get(v___x_1933_, 5);
v_messages_1940_ = lean_ctor_get(v___x_1933_, 6);
v_infoState_1941_ = lean_ctor_get(v___x_1933_, 7);
v_snapshotTasks_1942_ = lean_ctor_get(v___x_1933_, 8);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1972_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snapshotTasks_1942_);
lean_inc(v_infoState_1941_);
lean_inc(v_messages_1940_);
lean_inc(v_cache_1939_);
lean_inc(v_traceState_1934_);
lean_inc(v_auxDeclNGen_1938_);
lean_inc(v_ngen_1937_);
lean_inc(v_nextMacroScope_1936_);
lean_inc(v_env_1935_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1972_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint64_t v_tid_1946_; lean_object* v_traces_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1971_; 
v_tid_1946_ = lean_ctor_get_uint64(v_traceState_1934_, sizeof(void*)*1);
v_traces_1947_ = lean_ctor_get(v_traceState_1934_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_traceState_1934_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1949_ = v_traceState_1934_;
v_isShared_1950_ = v_isSharedCheck_1971_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_traces_1947_);
lean_dec(v_traceState_1934_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1971_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; double v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1953_ = 0;
v___x_1954_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1955_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1955_, 0, v_cls_1920_);
lean_ctor_set(v___x_1955_, 1, v___x_1951_);
lean_ctor_set(v___x_1955_, 2, v___x_1954_);
lean_ctor_set_float(v___x_1955_, sizeof(void*)*3, v___x_1952_);
lean_ctor_set_float(v___x_1955_, sizeof(void*)*3 + 8, v___x_1952_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*3 + 16, v___x_1953_);
v___x_1956_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1957_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v_a_1929_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
lean_inc(v_ref_1927_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_ref_1927_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l_Lean_PersistentArray_push___redArg(v_traces_1947_, v___x_1958_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1959_);
v___x_1961_ = v___x_1949_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1959_);
lean_ctor_set_uint64(v_reuseFailAlloc_1970_, sizeof(void*)*1, v_tid_1946_);
v___x_1961_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_1961_);
v___x_1963_ = v___x_1944_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_env_1935_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_nextMacroScope_1936_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_ngen_1937_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_auxDeclNGen_1938_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1969_, 5, v_cache_1939_);
lean_ctor_set(v_reuseFailAlloc_1969_, 6, v_messages_1940_);
lean_ctor_set(v_reuseFailAlloc_1969_, 7, v_infoState_1941_);
lean_ctor_set(v_reuseFailAlloc_1969_, 8, v_snapshotTasks_1942_);
v___x_1963_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = lean_st_ref_set(v___y_1925_, v___x_1963_);
v___x_1965_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1965_);
v___x_1967_ = v___x_1931_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1974_, lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1974_, v_msg_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_1986_, lean_object* v_as_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_usize_dec_lt(v_i_1989_, v_sz_1988_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec(v_traceClass_1986_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1990_);
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v_snd_1999_; lean_object* v_fst_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2035_; 
v_a_1998_ = lean_array_uget(v_as_1987_, v_i_1989_);
v_snd_1999_ = lean_ctor_get(v_a_1998_, 1);
v_fst_2000_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2002_ = v_a_1998_;
v_isShared_2003_ = v_isSharedCheck_2035_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_2000_);
lean_dec(v_a_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2035_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_num_2004_; lean_object* v_den_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2034_; 
v_num_2004_ = lean_ctor_get(v_snd_1999_, 0);
v_den_2005_ = lean_ctor_get(v_snd_1999_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_snd_1999_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2007_ = v_snd_1999_;
v_isShared_2008_ = v_isSharedCheck_2034_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_den_2005_);
lean_inc(v_num_2004_);
lean_dec(v_snd_1999_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2034_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2000_);
v___x_2011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2008_ == 0)
{
lean_ctor_set_tag(v___x_2007_, 7);
lean_ctor_set(v___x_2007_, 1, v___x_2011_);
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___y_2015_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_dec_eq(v_den_2005_, v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2027_ = l_Int_repr(v_num_2004_);
lean_dec(v_num_2004_);
v___x_2028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2029_ = lean_string_append(v___x_2027_, v___x_2028_);
v___x_2030_ = l_Nat_reprFast(v_den_2005_);
v___x_2031_ = lean_string_append(v___x_2029_, v___x_2030_);
lean_dec_ref(v___x_2030_);
v___y_2015_ = v___x_2031_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2032_; 
lean_dec(v_den_2005_);
v___x_2032_ = l_Int_repr(v_num_2004_);
lean_dec(v_num_2004_);
v___y_2015_ = v___x_2032_;
goto v___jp_2014_;
}
v___jp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___y_2015_);
v___x_2017_ = l_Lean_MessageData_ofFormat(v___x_2016_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 7);
lean_ctor_set(v___x_2002_, 1, v___x_2017_);
lean_ctor_set(v___x_2002_, 0, v___x_2013_);
v___x_2019_ = v___x_2002_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
lean_inc(v_traceClass_1986_);
v___x_2020_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_1986_, v___x_2019_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2020_) == 0)
{
size_t v___x_2021_; size_t v___x_2022_; 
lean_dec_ref_known(v___x_2020_, 1);
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_1989_, v___x_2021_);
v_i_1989_ = v___x_2022_;
v_b_1990_ = v___x_2009_;
goto _start;
}
else
{
lean_dec(v_traceClass_1986_);
return v___x_2020_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2036_, lean_object* v_as_2037_, lean_object* v_sz_2038_, lean_object* v_i_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
size_t v_sz_boxed_2046_; size_t v_i_boxed_2047_; lean_object* v_res_2048_; 
v_sz_boxed_2046_ = lean_unbox_usize(v_sz_2038_);
lean_dec(v_sz_2038_);
v_i_boxed_2047_ = lean_unbox_usize(v_i_2039_);
lean_dec(v_i_2039_);
v_res_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2036_, v_as_2037_, v_sz_boxed_2046_, v_i_boxed_2047_, v_b_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_as_2037_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2052_, lean_object* v_model_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_options_2062_; uint8_t v_hasTrace_2063_; 
v_options_2062_ = lean_ctor_get(v_a_2056_, 2);
v_hasTrace_2063_ = lean_ctor_get_uint8(v_options_2062_, sizeof(void*)*1);
if (v_hasTrace_2063_ == 0)
{
lean_dec(v_traceClass_2052_);
goto v___jp_2059_;
}
else
{
lean_object* v_inheritedTraceOptions_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_inheritedTraceOptions_2064_ = lean_ctor_get(v_a_2056_, 13);
v___x_2065_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2052_);
v___x_2066_ = l_Lean_Name_append(v___x_2065_, v_traceClass_2052_);
v___x_2067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2064_, v_options_2062_, v___x_2066_);
lean_dec(v___x_2066_);
if (v___x_2067_ == 0)
{
lean_dec(v_traceClass_2052_);
goto v___jp_2059_;
}
else
{
lean_object* v___x_2068_; size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_box(0);
v_sz_2069_ = lean_array_size(v_model_2053_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2052_, v_model_2053_, v_sz_2069_, v___x_2070_, v___x_2068_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2079_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2068_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
return v___x_2071_;
}
}
}
v___jp_2059_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2080_, lean_object* v_model_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2080_, v_model_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec_ref(v_model_2081_);
return v_res_2087_;
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
