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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isRoot(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_Goal_getGeneration(lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_39_);
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
lean_dec_ref(v_goal_82_);
return v_b_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_142_; 
lean_dec_ref(v_b_87_);
v_head_88_ = lean_ctor_get(v_as_x27_86_, 0);
v_tail_89_ = lean_ctor_get(v_as_x27_86_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_as_x27_86_);
if (v_isSharedCheck_142_ == 0)
{
v___x_91_ = v_as_x27_86_;
v_isShared_92_ = v_isSharedCheck_142_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_tail_89_);
lean_inc(v_head_88_);
lean_dec(v_as_x27_86_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_142_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___y_96_; uint8_t v___y_97_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_93_ = lean_box(0);
v___x_94_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
lean_inc(v_head_88_);
v___x_104_ = l_Lean_Expr_cleanupAnnotations(v_head_88_);
v___x_105_ = l_Lean_Expr_isApp(v___x_104_);
if (v___x_105_ == 0)
{
lean_dec_ref(v___x_104_);
lean_del_object(v___x_91_);
lean_dec(v_head_88_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
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
lean_del_object(v___x_91_);
lean_dec(v_head_88_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_object* v_arg_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_arg_111_ = lean_ctor_get(v___x_108_, 1);
lean_inc_ref(v_arg_111_);
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_108_);
v___x_113_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_113_ == 0)
{
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_107_);
lean_del_object(v___x_91_);
lean_dec(v_head_88_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_116_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__2));
v___x_117_ = l_Lean_Expr_isConstOf(v___x_115_, v___x_116_);
lean_dec_ref(v___x_115_);
if (v___x_117_ == 0)
{
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_107_);
lean_del_object(v___x_91_);
lean_dec(v_head_88_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_object* v___x_119_; 
lean_inc_ref(v_goal_82_);
v___x_119_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_head_88_);
lean_dec(v_head_88_);
if (lean_obj_tag(v___x_119_) == 1)
{
lean_object* v_val_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_val_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_120_);
lean_dec_ref(v___x_119_);
v___x_121_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__4));
v___x_122_ = l_Lean_Expr_isConstOf(v_val_120_, v___x_121_);
lean_dec(v_val_120_);
if (v___x_122_ == 0)
{
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_107_);
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_object* v___x_124_; 
lean_inc_ref(v_goal_82_);
v___x_124_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_arg_111_);
lean_dec_ref(v_arg_111_);
if (lean_obj_tag(v___x_124_) == 1)
{
lean_object* v_val_125_; lean_object* v___x_126_; 
v_val_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v___x_124_);
lean_inc_ref(v_goal_82_);
v___x_126_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_arg_107_);
lean_dec_ref(v_arg_107_);
if (lean_obj_tag(v___x_126_) == 1)
{
lean_object* v_val_127_; uint8_t v___y_129_; uint8_t v___y_134_; uint8_t v___x_136_; 
v_val_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_127_);
lean_dec_ref(v___x_126_);
v___x_136_ = lean_expr_eqv(v_val_125_, v_e_83_);
if (v___x_136_ == 0)
{
v___y_134_ = v___x_136_;
goto v___jp_133_;
}
else
{
uint8_t v___x_137_; 
lean_inc(v_v_85_);
v___x_137_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_84_, v_v_85_, v_val_127_);
if (v___x_137_ == 0)
{
v___y_134_ = v___x_136_;
goto v___jp_133_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = 0;
v___y_129_ = v___x_138_;
goto v___jp_128_;
}
}
v___jp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = lean_expr_eqv(v_val_127_, v_e_83_);
lean_dec(v_val_127_);
if (v___x_130_ == 0)
{
lean_dec(v_val_125_);
v___y_96_ = v___y_129_;
v___y_97_ = v___x_130_;
goto v___jp_95_;
}
else
{
uint8_t v___x_131_; 
lean_inc(v_v_85_);
v___x_131_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq(v_a_84_, v_v_85_, v_val_125_);
lean_dec(v_val_125_);
if (v___x_131_ == 0)
{
v___y_96_ = v___y_129_;
v___y_97_ = v___x_130_;
goto v___jp_95_;
}
else
{
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
}
}
v___jp_133_:
{
if (v___y_134_ == 0)
{
v___y_129_ = v___y_134_;
goto v___jp_128_;
}
else
{
lean_object* v___x_135_; 
lean_dec(v_val_127_);
lean_dec(v_val_125_);
lean_del_object(v___x_91_);
lean_dec(v_tail_89_);
lean_dec(v_v_85_);
lean_dec_ref(v_goal_82_);
v___x_135_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__6));
return v___x_135_;
}
}
}
else
{
lean_dec(v___x_126_);
lean_dec(v_val_125_);
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
}
else
{
lean_dec(v___x_124_);
lean_dec_ref(v_arg_107_);
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
}
}
else
{
lean_dec(v___x_119_);
lean_dec_ref(v_arg_111_);
lean_dec_ref(v_arg_107_);
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
}
}
}
}
v___jp_95_:
{
if (v___y_97_ == 0)
{
lean_del_object(v___x_91_);
v_as_x27_86_ = v_tail_89_;
v_b_87_ = v___x_94_;
goto _start;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
lean_dec(v_tail_89_);
lean_dec(v_v_85_);
lean_dec_ref(v_goal_82_);
v___x_99_ = lean_box(v___y_96_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 0);
lean_ctor_set(v___x_91_, 1, v___x_93_);
lean_ctor_set(v___x_91_, 0, v___x_100_);
v___x_102_ = v___x_91_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_93_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___boxed(lean_object* v_goal_143_, lean_object* v_e_144_, lean_object* v_a_145_, lean_object* v_v_146_, lean_object* v_as_x27_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_143_, v_e_144_, v_a_145_, v_v_146_, v_as_x27_147_, v_b_148_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_e_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_150_, lean_object* v_vals_151_, lean_object* v_i_152_, lean_object* v_k_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_keys_150_);
v___x_155_ = lean_nat_dec_lt(v_i_152_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_dec(v_i_152_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v_k_x27_157_; uint8_t v___x_158_; 
v_k_x27_157_ = lean_array_fget_borrowed(v_keys_150_, v_i_152_);
v___x_158_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_153_, v_k_x27_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_add(v_i_152_, v___x_159_);
lean_dec(v_i_152_);
v_i_152_ = v___x_160_;
goto _start;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_array_fget_borrowed(v_vals_151_, v_i_152_);
lean_dec(v_i_152_);
lean_inc(v___x_162_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_164_, lean_object* v_vals_165_, lean_object* v_i_166_, lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_164_, v_vals_165_, v_i_166_, v_k_167_);
lean_dec_ref(v_k_167_);
lean_dec_ref(v_vals_165_);
lean_dec_ref(v_keys_164_);
return v_res_168_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; 
v___x_169_ = ((size_t)5ULL);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_shift_left(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; 
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0);
v___x_174_ = lean_usize_sub(v___x_173_, v___x_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_175_, size_t v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v_es_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_199_; 
v_es_178_ = lean_ctor_get(v_x_175_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_175_);
if (v_isSharedCheck_199_ == 0)
{
v___x_180_ = v_x_175_;
v_isShared_181_ = v_isSharedCheck_199_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_es_178_);
lean_dec(v_x_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_199_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; lean_object* v_j_186_; lean_object* v___x_187_; 
v___x_182_ = lean_box(2);
v___x_183_ = ((size_t)5ULL);
v___x_184_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1);
v___x_185_ = lean_usize_land(v_x_176_, v___x_184_);
v_j_186_ = lean_usize_to_nat(v___x_185_);
v___x_187_ = lean_array_get(v___x_182_, v_es_178_, v_j_186_);
lean_dec(v_j_186_);
lean_dec_ref(v_es_178_);
switch(lean_obj_tag(v___x_187_))
{
case 0:
{
lean_object* v_key_188_; lean_object* v_val_189_; uint8_t v___x_190_; 
v_key_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_key_188_);
v_val_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_val_189_);
lean_dec_ref(v___x_187_);
v___x_190_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_177_, v_key_188_);
lean_dec(v_key_188_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec(v_val_189_);
lean_del_object(v___x_180_);
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v___x_193_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
lean_ctor_set(v___x_180_, 0, v_val_189_);
v___x_193_ = v___x_180_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_val_189_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
case 1:
{
lean_object* v_node_195_; size_t v___x_196_; 
lean_del_object(v___x_180_);
v_node_195_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_node_195_);
lean_dec_ref(v___x_187_);
v___x_196_ = lean_usize_shift_right(v_x_176_, v___x_183_);
v_x_175_ = v_node_195_;
v_x_176_ = v___x_196_;
goto _start;
}
default: 
{
lean_object* v___x_198_; 
lean_del_object(v___x_180_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
}
}
else
{
lean_object* v_ks_200_; lean_object* v_vs_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_ks_200_ = lean_ctor_get(v_x_175_, 0);
lean_inc_ref(v_ks_200_);
v_vs_201_ = lean_ctor_get(v_x_175_, 1);
lean_inc_ref(v_vs_201_);
lean_dec_ref(v_x_175_);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_200_, v_vs_201_, v___x_202_, v_x_177_);
lean_dec_ref(v_vs_201_);
lean_dec_ref(v_ks_200_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
size_t v_x_2627__boxed_207_; lean_object* v_res_208_; 
v_x_2627__boxed_207_ = lean_unbox_usize(v_x_205_);
lean_dec(v_x_205_);
v_res_208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_204_, v_x_2627__boxed_207_, v_x_206_);
lean_dec_ref(v_x_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint64_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_210_);
v___x_212_ = lean_uint64_to_usize(v___x_211_);
v___x_213_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_209_, v___x_212_, v_x_210_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg___boxed(lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_214_, v_x_215_);
lean_dec_ref(v_x_215_);
return v_res_216_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(lean_object* v_goal_217_, lean_object* v_a_218_, lean_object* v_e_219_, lean_object* v_v_220_){
_start:
{
lean_object* v_toGoalState_221_; lean_object* v_parents_222_; lean_object* v___x_223_; 
v_toGoalState_221_ = lean_ctor_get(v_goal_217_, 0);
v_parents_222_ = lean_ctor_get(v_toGoalState_221_, 4);
lean_inc_ref(v_parents_222_);
v___x_223_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_parents_222_, v_e_219_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_fst_228_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref(v___x_223_);
v___x_225_ = l_Lean_Meta_Grind_ParentSet_elems(v_val_224_);
lean_dec(v_val_224_);
v___x_226_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg___closed__0));
v___x_227_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_217_, v_e_219_, v_a_218_, v_v_220_, v___x_225_, v___x_226_);
v_fst_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_fst_228_);
lean_dec_ref(v___x_227_);
if (lean_obj_tag(v_fst_228_) == 0)
{
uint8_t v___x_229_; 
v___x_229_ = 1;
return v___x_229_;
}
else
{
lean_object* v_val_230_; uint8_t v___x_231_; 
v_val_230_ = lean_ctor_get(v_fst_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v_fst_228_);
v___x_231_ = lean_unbox(v_val_230_);
lean_dec(v_val_230_);
return v___x_231_;
}
}
else
{
uint8_t v___x_232_; 
lean_dec(v___x_223_);
lean_dec(v_v_220_);
lean_dec_ref(v_goal_217_);
v___x_232_ = 1;
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs___boxed(lean_object* v_goal_233_, lean_object* v_a_234_, lean_object* v_e_235_, lean_object* v_v_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_233_, v_a_234_, v_e_235_, v_v_236_);
lean_dec_ref(v_e_235_);
lean_dec_ref(v_a_234_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(lean_object* v_00_u03b2_239_, lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(v_x_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___boxed(lean_object* v_00_u03b2_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0(v_00_u03b2_243_, v_x_244_, v_x_245_);
lean_dec_ref(v_x_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(lean_object* v_goal_247_, lean_object* v_e_248_, lean_object* v_a_249_, lean_object* v_v_250_, lean_object* v_as_251_, lean_object* v_as_x27_252_, lean_object* v_b_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___redArg(v_goal_247_, v_e_248_, v_a_249_, v_v_250_, v_as_x27_252_, v_b_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1___boxed(lean_object* v_goal_256_, lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_v_259_, lean_object* v_as_260_, lean_object* v_as_x27_261_, lean_object* v_b_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__1(v_goal_256_, v_e_257_, v_a_258_, v_v_259_, v_as_260_, v_as_x27_261_, v_b_262_, v_a_263_);
lean_dec(v_as_260_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_e_257_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(lean_object* v_00_u03b2_265_, lean_object* v_x_266_, size_t v_x_267_, lean_object* v_x_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_266_, v_x_267_, v_x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
size_t v_x_2740__boxed_274_; lean_object* v_res_275_; 
v_x_2740__boxed_274_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_275_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_270_, v_x_271_, v_x_2740__boxed_274_, v_x_273_);
lean_dec_ref(v_x_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_276_, lean_object* v_keys_277_, lean_object* v_vals_278_, lean_object* v_heq_279_, lean_object* v_i_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_277_, v_vals_278_, v_i_280_, v_k_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_283_, lean_object* v_keys_284_, lean_object* v_vals_285_, lean_object* v_heq_286_, lean_object* v_i_287_, lean_object* v_k_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1(v_00_u03b2_283_, v_keys_284_, v_vals_285_, v_heq_286_, v_i_287_, v_k_288_);
lean_dec_ref(v_k_288_);
lean_dec_ref(v_vals_285_);
lean_dec_ref(v_keys_284_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(lean_object* v_a_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
else
{
lean_object* v_key_293_; lean_object* v_tail_294_; uint8_t v___x_295_; 
v_key_293_ = lean_ctor_get(v_x_291_, 0);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
v___x_295_ = lean_int_dec_eq(v_key_293_, v_a_290_);
if (v___x_295_ == 0)
{
v_x_291_ = v_tail_294_;
goto _start;
}
else
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_297_, v_x_298_);
lean_dec(v_x_298_);
lean_dec(v_a_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_301_; lean_object* v_intZero_302_; 
v_natZero_301_ = lean_unsigned_to_nat(0u);
v_intZero_302_ = lean_nat_to_int(v_natZero_301_);
return v_intZero_302_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(lean_object* v_m_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_buckets_305_; lean_object* v___x_306_; uint64_t v___y_308_; lean_object* v_intZero_322_; uint8_t v_isNeg_323_; 
v_buckets_305_ = lean_ctor_get(v_m_303_, 1);
v___x_306_ = lean_array_get_size(v_buckets_305_);
v_intZero_322_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_323_ = lean_int_dec_lt(v_a_304_, v_intZero_322_);
if (v_isNeg_323_ == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint64_t v___x_327_; 
v_a_324_ = lean_nat_abs(v_a_304_);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_nat_mul(v___x_325_, v_a_324_);
lean_dec(v_a_324_);
v___x_327_ = lean_uint64_of_nat(v___x_326_);
lean_dec(v___x_326_);
v___y_308_ = v___x_327_;
goto v___jp_307_;
}
else
{
lean_object* v_abs_328_; lean_object* v_one_329_; lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint64_t v___x_334_; 
v_abs_328_ = lean_nat_abs(v_a_304_);
v_one_329_ = lean_unsigned_to_nat(1u);
v_a_330_ = lean_nat_sub(v_abs_328_, v_one_329_);
lean_dec(v_abs_328_);
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = lean_nat_mul(v___x_331_, v_a_330_);
lean_dec(v_a_330_);
v___x_333_ = lean_nat_add(v___x_332_, v_one_329_);
lean_dec(v___x_332_);
v___x_334_ = lean_uint64_of_nat(v___x_333_);
lean_dec(v___x_333_);
v___y_308_ = v___x_334_;
goto v___jp_307_;
}
v___jp_307_:
{
uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v_fold_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_309_ = 32ULL;
v___x_310_ = lean_uint64_shift_right(v___y_308_, v___x_309_);
v_fold_311_ = lean_uint64_xor(v___y_308_, v___x_310_);
v___x_312_ = 16ULL;
v___x_313_ = lean_uint64_shift_right(v_fold_311_, v___x_312_);
v___x_314_ = lean_uint64_xor(v_fold_311_, v___x_313_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = lean_usize_of_nat(v___x_306_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_sub(v___x_316_, v___x_317_);
v___x_319_ = lean_usize_land(v___x_315_, v___x_318_);
v___x_320_ = lean_array_uget_borrowed(v_buckets_305_, v___x_319_);
v___x_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_304_, v___x_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___boxed(lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_m_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(lean_object* v_goal_341_, lean_object* v_a_342_, lean_object* v_e_343_, lean_object* v_alreadyUsed_344_, lean_object* v_next_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_alreadyUsed_344_, v_next_345_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
lean_inc(v_next_345_);
lean_inc_ref(v_goal_341_);
v___x_347_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs(v_goal_341_, v_a_342_, v_e_343_, v_next_345_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_349_ = lean_int_add(v_next_345_, v___x_348_);
lean_dec(v_next_345_);
v_next_345_ = v___x_349_;
goto _start;
}
else
{
lean_dec_ref(v_goal_341_);
return v_next_345_;
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_352_ = lean_int_add(v_next_345_, v___x_351_);
lean_dec(v_next_345_);
v_next_345_ = v___x_352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___boxed(lean_object* v_goal_354_, lean_object* v_a_355_, lean_object* v_e_356_, lean_object* v_alreadyUsed_357_, lean_object* v_next_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_354_, v_a_355_, v_e_356_, v_alreadyUsed_357_, v_next_358_);
lean_dec_ref(v_alreadyUsed_357_);
lean_dec_ref(v_e_356_);
lean_dec_ref(v_a_355_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(lean_object* v_00_u03b2_360_, lean_object* v_m_361_, lean_object* v_a_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg(v_m_361_, v_a_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___boxed(lean_object* v_00_u03b2_364_, lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0(v_00_u03b2_364_, v_m_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_m_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(lean_object* v_00_u03b2_369_, lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_373_, lean_object* v_a_374_, lean_object* v_x_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0(v_00_u03b2_373_, v_a_374_, v_x_375_);
lean_dec(v_x_375_);
lean_dec(v_a_374_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue(lean_object* v_goal_378_, lean_object* v_a_379_, lean_object* v_e_380_, lean_object* v_next_381_, lean_object* v_alreadyUsed_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_378_, v_a_379_, v_e_380_, v_alreadyUsed_382_, v_next_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_pickUnusedValue___boxed(lean_object* v_goal_384_, lean_object* v_a_385_, lean_object* v_e_386_, lean_object* v_next_387_, lean_object* v_alreadyUsed_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Grind_Arith_pickUnusedValue(v_goal_384_, v_a_385_, v_e_386_, v_next_387_, v_alreadyUsed_388_);
lean_dec_ref(v_alreadyUsed_388_);
lean_dec_ref(v_e_386_);
lean_dec_ref(v_a_385_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_473_){
_start:
{
uint8_t v___y_475_; uint8_t v___x_510_; 
lean_inc_ref(v_e_473_);
v___x_510_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_473_);
if (v___x_510_ == 0)
{
uint8_t v___x_511_; 
lean_inc_ref(v_e_473_);
v___x_511_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_473_);
v___y_475_ = v___x_511_;
goto v___jp_474_;
}
else
{
v___y_475_ = v___x_510_;
goto v___jp_474_;
}
v___jp_474_:
{
if (v___y_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_477_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5));
v___x_479_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8));
v___x_481_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11));
v___x_483_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14));
v___x_485_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17));
v___x_487_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20));
v___x_489_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23));
v___x_491_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26));
v___x_493_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29));
v___x_495_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32));
v___x_497_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_496_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Expr_isIte(v_e_473_);
if (v___x_498_ == 0)
{
uint8_t v___x_499_; 
v___x_499_ = l_Lean_Expr_isDIte(v_e_473_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35));
v___x_501_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_503_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_505_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47));
v___x_507_ = l_Lean_Expr_isAppOf(v_e_473_, v___x_506_);
if (v___x_507_ == 0)
{
if (lean_obj_tag(v_e_473_) == 9)
{
lean_object* v_a_508_; 
v_a_508_ = lean_ctor_get(v_e_473_, 0);
lean_inc_ref(v_a_508_);
lean_dec_ref(v_e_473_);
if (lean_obj_tag(v_a_508_) == 0)
{
uint8_t v___x_509_; 
lean_dec_ref(v_a_508_);
v___x_509_ = 1;
return v___x_509_;
}
else
{
lean_dec_ref(v_a_508_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_505_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_503_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_501_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_499_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_498_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_497_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_493_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_491_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_489_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_485_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_483_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_481_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_479_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_e_473_);
return v___y_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_512_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
return v_x_515_;
}
else
{
lean_object* v_key_517_; lean_object* v_value_518_; lean_object* v_tail_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_542_; 
v_key_517_ = lean_ctor_get(v_x_516_, 0);
v_value_518_ = lean_ctor_get(v_x_516_, 1);
v_tail_519_ = lean_ctor_get(v_x_516_, 2);
v_isSharedCheck_542_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_542_ == 0)
{
v___x_521_ = v_x_516_;
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_tail_519_);
lean_inc(v_value_518_);
lean_inc(v_key_517_);
lean_dec(v_x_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_542_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v_fold_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_523_ = lean_array_get_size(v_x_515_);
v___x_524_ = l_Lean_Expr_hash(v_key_517_);
v___x_525_ = 32ULL;
v___x_526_ = lean_uint64_shift_right(v___x_524_, v___x_525_);
v_fold_527_ = lean_uint64_xor(v___x_524_, v___x_526_);
v___x_528_ = 16ULL;
v___x_529_ = lean_uint64_shift_right(v_fold_527_, v___x_528_);
v___x_530_ = lean_uint64_xor(v_fold_527_, v___x_529_);
v___x_531_ = lean_uint64_to_usize(v___x_530_);
v___x_532_ = lean_usize_of_nat(v___x_523_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_usize_land(v___x_531_, v___x_534_);
v___x_536_ = lean_array_uget_borrowed(v_x_515_, v___x_535_);
lean_inc(v___x_536_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 2, v___x_536_);
v___x_538_ = v___x_521_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_key_517_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_value_518_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v___x_536_);
v___x_538_ = v_reuseFailAlloc_541_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_array_uset(v_x_515_, v___x_535_, v___x_538_);
v_x_515_ = v___x_539_;
v_x_516_ = v_tail_519_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_543_, lean_object* v_source_544_, lean_object* v_target_545_){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_array_get_size(v_source_544_);
v___x_547_ = lean_nat_dec_lt(v_i_543_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec_ref(v_source_544_);
lean_dec(v_i_543_);
return v_target_545_;
}
else
{
lean_object* v_es_548_; lean_object* v___x_549_; lean_object* v_source_550_; lean_object* v_target_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_es_548_ = lean_array_fget(v_source_544_, v_i_543_);
v___x_549_ = lean_box(0);
v_source_550_ = lean_array_fset(v_source_544_, v_i_543_, v___x_549_);
v_target_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_545_, v_es_548_);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v_i_543_, v___x_552_);
lean_dec(v_i_543_);
v_i_543_ = v___x_553_;
v_source_544_ = v_source_550_;
v_target_545_ = v_target_551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_nbuckets_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_556_ = lean_array_get_size(v_data_555_);
v___x_557_ = lean_unsigned_to_nat(2u);
v_nbuckets_558_ = lean_nat_mul(v___x_556_, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_box(0);
v___x_561_ = lean_mk_array(v_nbuckets_558_, v___x_560_);
v___x_562_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_559_, v_data_555_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_563_, lean_object* v_b_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_dec(v_b_564_);
lean_dec_ref(v_a_563_);
return v_x_565_;
}
else
{
lean_object* v_key_566_; lean_object* v_value_567_; lean_object* v_tail_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_580_; 
v_key_566_ = lean_ctor_get(v_x_565_, 0);
v_value_567_ = lean_ctor_get(v_x_565_, 1);
v_tail_568_ = lean_ctor_get(v_x_565_, 2);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_565_);
if (v_isSharedCheck_580_ == 0)
{
v___x_570_ = v_x_565_;
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_tail_568_);
lean_inc(v_value_567_);
lean_inc(v_key_566_);
lean_dec(v_x_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_580_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_expr_eqv(v_key_566_, v_a_563_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_563_, v_b_564_, v_tail_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_key_566_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_value_567_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_578_; 
lean_dec(v_value_567_);
lean_dec(v_key_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_b_564_);
lean_ctor_set(v___x_570_, 0, v_a_563_);
v___x_578_ = v___x_570_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_b_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_tail_568_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 0;
return v___x_583_;
}
else
{
lean_object* v_key_584_; lean_object* v_tail_585_; uint8_t v___x_586_; 
v_key_584_ = lean_ctor_get(v_x_582_, 0);
v_tail_585_ = lean_ctor_get(v_x_582_, 2);
v___x_586_ = lean_expr_eqv(v_key_584_, v_a_581_);
if (v___x_586_ == 0)
{
v_x_582_ = v_tail_585_;
goto _start;
}
else
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_588_, v_x_589_);
lean_dec(v_x_589_);
lean_dec_ref(v_a_588_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_592_, lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
lean_object* v_size_595_; lean_object* v_buckets_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_639_; 
v_size_595_ = lean_ctor_get(v_m_592_, 0);
v_buckets_596_ = lean_ctor_get(v_m_592_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_m_592_);
if (v_isSharedCheck_639_ == 0)
{
v___x_598_ = v_m_592_;
v_isShared_599_ = v_isSharedCheck_639_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_buckets_596_);
lean_inc(v_size_595_);
lean_dec(v_m_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_639_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v_fold_604_; uint64_t v___x_605_; uint64_t v___x_606_; uint64_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v_bkt_613_; uint8_t v___x_614_; 
v___x_600_ = lean_array_get_size(v_buckets_596_);
v___x_601_ = l_Lean_Expr_hash(v_a_593_);
v___x_602_ = 32ULL;
v___x_603_ = lean_uint64_shift_right(v___x_601_, v___x_602_);
v_fold_604_ = lean_uint64_xor(v___x_601_, v___x_603_);
v___x_605_ = 16ULL;
v___x_606_ = lean_uint64_shift_right(v_fold_604_, v___x_605_);
v___x_607_ = lean_uint64_xor(v_fold_604_, v___x_606_);
v___x_608_ = lean_uint64_to_usize(v___x_607_);
v___x_609_ = lean_usize_of_nat(v___x_600_);
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_sub(v___x_609_, v___x_610_);
v___x_612_ = lean_usize_land(v___x_608_, v___x_611_);
v_bkt_613_ = lean_array_uget_borrowed(v_buckets_596_, v___x_612_);
v___x_614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_593_, v_bkt_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v_size_x27_616_; lean_object* v___x_617_; lean_object* v_buckets_x27_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v_size_x27_616_ = lean_nat_add(v_size_595_, v___x_615_);
lean_dec(v_size_595_);
lean_inc(v_bkt_613_);
v___x_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_617_, 0, v_a_593_);
lean_ctor_set(v___x_617_, 1, v_b_594_);
lean_ctor_set(v___x_617_, 2, v_bkt_613_);
v_buckets_x27_618_ = lean_array_uset(v_buckets_596_, v___x_612_, v___x_617_);
v___x_619_ = lean_unsigned_to_nat(4u);
v___x_620_ = lean_nat_mul(v_size_x27_616_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(3u);
v___x_622_ = lean_nat_div(v___x_620_, v___x_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_array_get_size(v_buckets_x27_618_);
v___x_624_ = lean_nat_dec_le(v___x_622_, v___x_623_);
lean_dec(v___x_622_);
if (v___x_624_ == 0)
{
lean_object* v_val_625_; lean_object* v___x_627_; 
v_val_625_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_618_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_val_625_);
lean_ctor_set(v___x_598_, 0, v_size_x27_616_);
v___x_627_ = v___x_598_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_size_x27_616_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_val_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_630_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_buckets_x27_618_);
lean_ctor_set(v___x_598_, 0, v_size_x27_616_);
v___x_630_ = v___x_598_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_size_x27_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_buckets_x27_618_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v_buckets_x27_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc(v_bkt_613_);
v___x_632_ = lean_box(0);
v_buckets_x27_633_ = lean_array_uset(v_buckets_596_, v___x_612_, v___x_632_);
v___x_634_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_593_, v_b_594_, v_bkt_613_);
v___x_635_ = lean_array_uset(v_buckets_x27_633_, v___x_612_, v___x_634_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_635_);
v___x_637_ = v___x_598_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_size_595_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_640_, lean_object* v_as_x27_641_, lean_object* v_b_642_){
_start:
{
if (lean_obj_tag(v_as_x27_641_) == 0)
{
lean_dec_ref(v_v_640_);
return v_b_642_;
}
else
{
lean_object* v_head_643_; lean_object* v_tail_644_; lean_object* v___x_645_; 
v_head_643_ = lean_ctor_get(v_as_x27_641_, 0);
lean_inc(v_head_643_);
v_tail_644_ = lean_ctor_get(v_as_x27_641_, 1);
lean_inc(v_tail_644_);
lean_dec_ref(v_as_x27_641_);
lean_inc_ref(v_v_640_);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_642_, v_head_643_, v_v_640_);
v_as_x27_641_ = v_tail_644_;
v_b_642_ = v___x_645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_647_, lean_object* v_e_648_, lean_object* v_v_649_, lean_object* v_a_650_){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = 0;
v___x_652_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_647_, v_e_648_, v___x_651_);
v___x_653_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_649_, v___x_652_, v_a_650_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_654_, lean_object* v_m_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_655_, v_a_656_, v_b_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_659_, lean_object* v_as_660_, lean_object* v_as_x27_661_, lean_object* v_b_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_659_, v_as_x27_661_, v_b_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_665_, lean_object* v_as_666_, lean_object* v_as_x27_667_, lean_object* v_b_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_665_, v_as_666_, v_as_x27_667_, v_b_668_, v_a_669_);
lean_dec(v_as_666_);
return v_res_670_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_671_, lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_675_, lean_object* v_a_676_, lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_675_, v_a_676_, v_x_677_);
lean_dec(v_x_677_);
lean_dec_ref(v_a_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_680_, lean_object* v_data_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_684_, v_b_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_688_, lean_object* v_i_689_, lean_object* v_source_690_, lean_object* v_target_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_689_, v_source_690_, v_target_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_698_) == 0)
{
return v_x_697_;
}
else
{
lean_object* v_key_699_; lean_object* v_value_700_; lean_object* v_tail_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_738_; 
v_key_699_ = lean_ctor_get(v_x_698_, 0);
v_value_700_ = lean_ctor_get(v_x_698_, 1);
v_tail_701_ = lean_ctor_get(v_x_698_, 2);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_698_);
if (v_isSharedCheck_738_ == 0)
{
v___x_703_ = v_x_698_;
v_isShared_704_ = v_isSharedCheck_738_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_tail_701_);
lean_inc(v_value_700_);
lean_inc(v_key_699_);
lean_dec(v_x_698_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_738_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint64_t v___y_707_; lean_object* v_intZero_725_; uint8_t v_isNeg_726_; 
v___x_705_ = lean_array_get_size(v_x_697_);
v_intZero_725_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_726_ = lean_int_dec_lt(v_key_699_, v_intZero_725_);
if (v_isNeg_726_ == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint64_t v___x_730_; 
v_a_727_ = lean_nat_abs(v_key_699_);
v___x_728_ = lean_unsigned_to_nat(2u);
v___x_729_ = lean_nat_mul(v___x_728_, v_a_727_);
lean_dec(v_a_727_);
v___x_730_ = lean_uint64_of_nat(v___x_729_);
lean_dec(v___x_729_);
v___y_707_ = v___x_730_;
goto v___jp_706_;
}
else
{
lean_object* v_abs_731_; lean_object* v_one_732_; lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint64_t v___x_737_; 
v_abs_731_ = lean_nat_abs(v_key_699_);
v_one_732_ = lean_unsigned_to_nat(1u);
v_a_733_ = lean_nat_sub(v_abs_731_, v_one_732_);
lean_dec(v_abs_731_);
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_mul(v___x_734_, v_a_733_);
lean_dec(v_a_733_);
v___x_736_ = lean_nat_add(v___x_735_, v_one_732_);
lean_dec(v___x_735_);
v___x_737_ = lean_uint64_of_nat(v___x_736_);
lean_dec(v___x_736_);
v___y_707_ = v___x_737_;
goto v___jp_706_;
}
v___jp_706_:
{
uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v_fold_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_708_ = 32ULL;
v___x_709_ = lean_uint64_shift_right(v___y_707_, v___x_708_);
v_fold_710_ = lean_uint64_xor(v___y_707_, v___x_709_);
v___x_711_ = 16ULL;
v___x_712_ = lean_uint64_shift_right(v_fold_710_, v___x_711_);
v___x_713_ = lean_uint64_xor(v_fold_710_, v___x_712_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = lean_usize_of_nat(v___x_705_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_sub(v___x_715_, v___x_716_);
v___x_718_ = lean_usize_land(v___x_714_, v___x_717_);
v___x_719_ = lean_array_uget_borrowed(v_x_697_, v___x_718_);
lean_inc(v___x_719_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 2, v___x_719_);
v___x_721_ = v___x_703_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_key_699_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_value_700_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___x_719_);
v___x_721_ = v_reuseFailAlloc_724_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; 
v___x_722_ = lean_array_uset(v_x_697_, v___x_718_, v___x_721_);
v_x_697_ = v___x_722_;
v_x_698_ = v_tail_701_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_739_, lean_object* v_source_740_, lean_object* v_target_741_){
_start:
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_get_size(v_source_740_);
v___x_743_ = lean_nat_dec_lt(v_i_739_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec_ref(v_source_740_);
lean_dec(v_i_739_);
return v_target_741_;
}
else
{
lean_object* v_es_744_; lean_object* v___x_745_; lean_object* v_source_746_; lean_object* v_target_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_es_744_ = lean_array_fget(v_source_740_, v_i_739_);
v___x_745_ = lean_box(0);
v_source_746_ = lean_array_fset(v_source_740_, v_i_739_, v___x_745_);
v_target_747_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_741_, v_es_744_);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_i_739_, v___x_748_);
lean_dec(v_i_739_);
v_i_739_ = v___x_749_;
v_source_740_ = v_source_746_;
v_target_741_ = v_target_747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_751_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_nbuckets_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_752_ = lean_array_get_size(v_data_751_);
v___x_753_ = lean_unsigned_to_nat(2u);
v_nbuckets_754_ = lean_nat_mul(v___x_752_, v___x_753_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_box(0);
v___x_757_ = lean_mk_array(v_nbuckets_754_, v___x_756_);
v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_755_, v_data_751_, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_b_761_){
_start:
{
lean_object* v_size_762_; lean_object* v_buckets_763_; lean_object* v___x_764_; uint64_t v___y_766_; lean_object* v_intZero_803_; uint8_t v_isNeg_804_; 
v_size_762_ = lean_ctor_get(v_m_759_, 0);
v_buckets_763_ = lean_ctor_get(v_m_759_, 1);
v___x_764_ = lean_array_get_size(v_buckets_763_);
v_intZero_803_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_804_ = lean_int_dec_lt(v_a_760_, v_intZero_803_);
if (v_isNeg_804_ == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint64_t v___x_808_; 
v_a_805_ = lean_nat_abs(v_a_760_);
v___x_806_ = lean_unsigned_to_nat(2u);
v___x_807_ = lean_nat_mul(v___x_806_, v_a_805_);
lean_dec(v_a_805_);
v___x_808_ = lean_uint64_of_nat(v___x_807_);
lean_dec(v___x_807_);
v___y_766_ = v___x_808_;
goto v___jp_765_;
}
else
{
lean_object* v_abs_809_; lean_object* v_one_810_; lean_object* v_a_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint64_t v___x_815_; 
v_abs_809_ = lean_nat_abs(v_a_760_);
v_one_810_ = lean_unsigned_to_nat(1u);
v_a_811_ = lean_nat_sub(v_abs_809_, v_one_810_);
lean_dec(v_abs_809_);
v___x_812_ = lean_unsigned_to_nat(2u);
v___x_813_ = lean_nat_mul(v___x_812_, v_a_811_);
lean_dec(v_a_811_);
v___x_814_ = lean_nat_add(v___x_813_, v_one_810_);
lean_dec(v___x_813_);
v___x_815_ = lean_uint64_of_nat(v___x_814_);
lean_dec(v___x_814_);
v___y_766_ = v___x_815_;
goto v___jp_765_;
}
v___jp_765_:
{
uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v_fold_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_bkt_778_; uint8_t v___x_779_; 
v___x_767_ = 32ULL;
v___x_768_ = lean_uint64_shift_right(v___y_766_, v___x_767_);
v_fold_769_ = lean_uint64_xor(v___y_766_, v___x_768_);
v___x_770_ = 16ULL;
v___x_771_ = lean_uint64_shift_right(v_fold_769_, v___x_770_);
v___x_772_ = lean_uint64_xor(v_fold_769_, v___x_771_);
v___x_773_ = lean_uint64_to_usize(v___x_772_);
v___x_774_ = lean_usize_of_nat(v___x_764_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_sub(v___x_774_, v___x_775_);
v___x_777_ = lean_usize_land(v___x_773_, v___x_776_);
v_bkt_778_ = lean_array_uget_borrowed(v_buckets_763_, v___x_777_);
v___x_779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_760_, v_bkt_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_800_; 
lean_inc_ref(v_buckets_763_);
lean_inc(v_size_762_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_m_759_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v_m_759_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_m_759_, 0);
lean_dec(v_unused_802_);
v___x_781_ = v_m_759_;
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_m_759_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_800_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_size_x27_784_; lean_object* v___x_785_; lean_object* v_buckets_x27_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v_size_x27_784_ = lean_nat_add(v_size_762_, v___x_783_);
lean_dec(v_size_762_);
lean_inc(v_bkt_778_);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v_a_760_);
lean_ctor_set(v___x_785_, 1, v_b_761_);
lean_ctor_set(v___x_785_, 2, v_bkt_778_);
v_buckets_x27_786_ = lean_array_uset(v_buckets_763_, v___x_777_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(4u);
v___x_788_ = lean_nat_mul(v_size_x27_784_, v___x_787_);
v___x_789_ = lean_unsigned_to_nat(3u);
v___x_790_ = lean_nat_div(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_array_get_size(v_buckets_x27_786_);
v___x_792_ = lean_nat_dec_le(v___x_790_, v___x_791_);
lean_dec(v___x_790_);
if (v___x_792_ == 0)
{
lean_object* v_val_793_; lean_object* v___x_795_; 
v_val_793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_786_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_val_793_);
lean_ctor_set(v___x_781_, 0, v_size_x27_784_);
v___x_795_ = v___x_781_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_size_x27_784_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_val_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
lean_object* v___x_798_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_buckets_x27_786_);
lean_ctor_set(v___x_781_, 0, v_size_x27_784_);
v___x_798_ = v___x_781_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_size_x27_784_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_buckets_x27_786_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_dec(v_b_761_);
lean_dec(v_a_760_);
return v_m_759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_816_, lean_object* v_isTarget_817_, lean_object* v_as_818_, size_t v_sz_819_, size_t v_i_820_, lean_object* v_b_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_lt(v_i_820_, v_sz_819_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v_isTarget_817_);
lean_dec_ref(v_goal_816_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_821_);
return v___x_828_;
}
else
{
lean_object* v_snd_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_911_; 
v_snd_829_ = lean_ctor_get(v_b_821_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_b_821_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v_b_821_, 0);
lean_dec(v_unused_912_);
v___x_831_ = v_b_821_;
v_isShared_832_ = v_isSharedCheck_911_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_snd_829_);
lean_dec(v_b_821_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_911_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_array_uget_borrowed(v_as_818_, v_i_820_);
lean_inc(v_a_833_);
lean_inc_ref(v_goal_816_);
v___x_834_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_816_, v_a_833_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_snd_835_; lean_object* v_a_836_; lean_object* v_fst_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_901_; 
v_snd_835_ = lean_ctor_get(v_snd_829_, 1);
lean_inc(v_snd_835_);
v_a_836_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_834_);
v_fst_837_ = lean_ctor_get(v_snd_829_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_snd_829_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_snd_829_, 1);
lean_dec(v_unused_902_);
v___x_839_ = v_snd_829_;
v_isShared_840_ = v_isSharedCheck_901_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_fst_837_);
lean_dec(v_snd_829_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_901_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_900_; 
v_fst_841_ = lean_ctor_get(v_snd_835_, 0);
v_snd_842_ = lean_ctor_get(v_snd_835_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_snd_835_);
if (v_isSharedCheck_900_ == 0)
{
v___x_844_ = v_snd_835_;
v_isShared_845_ = v_isSharedCheck_900_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_842_);
lean_inc(v_fst_841_);
lean_dec(v_snd_835_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_900_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_a_848_; uint8_t v___x_855_; 
v___x_846_ = lean_box(0);
v___x_855_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_836_);
if (v___x_855_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v_a_836_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_snd_842_);
lean_ctor_set(v___x_839_, 0, v_fst_841_);
v___x_857_ = v___x_839_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_841_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_842_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_857_);
lean_ctor_set(v___x_831_, 0, v_fst_837_);
v___x_859_ = v___x_831_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_837_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
v_a_848_ = v___x_859_;
goto v___jp_847_;
}
}
}
else
{
lean_object* v___x_862_; 
lean_inc_ref(v_isTarget_817_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v_a_836_);
v___x_862_ = lean_apply_6(v_isTarget_817_, v_a_836_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, lean_box(0));
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; uint8_t v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_866_; 
lean_dec(v_a_836_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_snd_842_);
lean_ctor_set(v___x_839_, 0, v_fst_841_);
v___x_866_ = v___x_839_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_fst_841_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_842_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_866_);
lean_ctor_set(v___x_831_, 0, v_fst_837_);
v___x_868_ = v___x_831_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fst_837_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
v_a_848_ = v___x_868_;
goto v___jp_847_;
}
}
}
else
{
lean_object* v_self_871_; lean_object* v___x_872_; 
v_self_871_ = lean_ctor_get(v_a_836_, 0);
lean_inc_ref(v_self_871_);
lean_dec(v_a_836_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_842_, v_self_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
lean_inc_ref(v_goal_816_);
v___x_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_816_, v_snd_842_, v_self_871_, v_fst_841_, v_fst_837_);
lean_inc(v___x_873_);
v___x_874_ = l_Rat_ofInt(v___x_873_);
lean_inc_ref(v_goal_816_);
v___x_875_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_816_, v_self_871_, v___x_874_, v_snd_842_);
v___x_876_ = lean_box(0);
lean_inc(v___x_873_);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_841_, v___x_873_, v___x_876_);
v___x_878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_879_ = lean_int_add(v___x_873_, v___x_878_);
lean_dec(v___x_873_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_875_);
lean_ctor_set(v___x_839_, 0, v___x_877_);
v___x_881_ = v___x_839_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_875_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_881_);
lean_ctor_set(v___x_831_, 0, v___x_879_);
v___x_883_ = v___x_831_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
v_a_848_ = v___x_883_;
goto v___jp_847_;
}
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref(v___x_872_);
lean_dec_ref(v_self_871_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v_snd_842_);
lean_ctor_set(v___x_839_, 0, v_fst_841_);
v___x_887_ = v___x_839_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_841_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_842_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_887_);
lean_ctor_set(v___x_831_, 0, v_fst_837_);
v___x_889_ = v___x_831_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_837_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_848_ = v___x_889_;
goto v___jp_847_;
}
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v_fst_841_);
lean_del_object(v___x_839_);
lean_dec(v_fst_837_);
lean_dec(v_a_836_);
lean_del_object(v___x_831_);
lean_dec_ref(v_isTarget_817_);
lean_dec_ref(v_goal_816_);
v_a_892_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_862_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_862_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
v___jp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_848_);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_848_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_820_, v___x_851_);
v_i_820_ = v___x_852_;
v_b_821_ = v___x_850_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_831_);
lean_dec(v_snd_829_);
lean_dec_ref(v_isTarget_817_);
lean_dec_ref(v_goal_816_);
v_a_903_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_834_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_834_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_913_, lean_object* v_isTarget_914_, lean_object* v_as_915_, lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
size_t v_sz_boxed_924_; size_t v_i_boxed_925_; lean_object* v_res_926_; 
v_sz_boxed_924_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_925_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_913_, v_isTarget_914_, v_as_915_, v_sz_boxed_924_, v_i_boxed_925_, v_b_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v_as_915_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_927_, lean_object* v_isTarget_928_, lean_object* v_as_929_, size_t v_sz_930_, size_t v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_931_, v_sz_930_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v_isTarget_928_);
lean_dec_ref(v_goal_927_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_932_);
return v___x_939_;
}
else
{
lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_1022_; 
v_snd_940_ = lean_ctor_get(v_b_932_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_b_932_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_b_932_, 0);
lean_dec(v_unused_1023_);
v___x_942_ = v_b_932_;
v_isShared_943_ = v_isSharedCheck_1022_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_dec(v_b_932_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_1022_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_a_944_; lean_object* v___x_945_; 
v_a_944_ = lean_array_uget_borrowed(v_as_929_, v_i_931_);
lean_inc(v_a_944_);
lean_inc_ref(v_goal_927_);
v___x_945_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_927_, v_a_944_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_snd_946_; lean_object* v_a_947_; lean_object* v_fst_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1012_; 
v_snd_946_ = lean_ctor_get(v_snd_940_, 1);
lean_inc(v_snd_946_);
v_a_947_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_945_);
v_fst_948_ = lean_ctor_get(v_snd_940_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_snd_940_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_snd_940_, 1);
lean_dec(v_unused_1013_);
v___x_950_ = v_snd_940_;
v_isShared_951_ = v_isSharedCheck_1012_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_fst_948_);
lean_dec(v_snd_940_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1012_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1011_; 
v_fst_952_ = lean_ctor_get(v_snd_946_, 0);
v_snd_953_ = lean_ctor_get(v_snd_946_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_snd_946_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_955_ = v_snd_946_;
v_isShared_956_ = v_isSharedCheck_1011_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_inc(v_fst_952_);
lean_dec(v_snd_946_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1011_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_a_959_; uint8_t v___x_966_; 
v___x_957_ = lean_box(0);
v___x_966_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_947_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v_a_947_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_snd_953_);
lean_ctor_set(v___x_950_, 0, v_fst_952_);
v___x_968_ = v___x_950_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_snd_953_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_968_);
lean_ctor_set(v___x_942_, 0, v_fst_948_);
v___x_970_ = v___x_942_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_a_959_ = v___x_970_;
goto v___jp_958_;
}
}
}
else
{
lean_object* v___x_973_; 
lean_inc_ref(v_isTarget_928_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v_a_947_);
v___x_973_ = lean_apply_6(v_isTarget_928_, v_a_947_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, lean_box(0));
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; uint8_t v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = lean_unbox(v_a_974_);
lean_dec(v_a_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_977_; 
lean_dec(v_a_947_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_snd_953_);
lean_ctor_set(v___x_950_, 0, v_fst_952_);
v___x_977_ = v___x_950_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_snd_953_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_977_);
lean_ctor_set(v___x_942_, 0, v_fst_948_);
v___x_979_ = v___x_942_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
v_a_959_ = v___x_979_;
goto v___jp_958_;
}
}
}
else
{
lean_object* v_self_982_; lean_object* v___x_983_; 
v_self_982_ = lean_ctor_get(v_a_947_, 0);
lean_inc_ref(v_self_982_);
lean_dec(v_a_947_);
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_953_, v_self_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
lean_inc_ref(v_goal_927_);
v___x_984_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_927_, v_snd_953_, v_self_982_, v_fst_952_, v_fst_948_);
lean_inc(v___x_984_);
v___x_985_ = l_Rat_ofInt(v___x_984_);
lean_inc_ref(v_goal_927_);
v___x_986_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_927_, v_self_982_, v___x_985_, v_snd_953_);
v___x_987_ = lean_box(0);
lean_inc(v___x_984_);
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_952_, v___x_984_, v___x_987_);
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_990_ = lean_int_add(v___x_984_, v___x_989_);
lean_dec(v___x_984_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___x_986_);
lean_ctor_set(v___x_950_, 0, v___x_988_);
v___x_992_ = v___x_950_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_986_);
v___x_992_ = v_reuseFailAlloc_996_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_992_);
lean_ctor_set(v___x_942_, 0, v___x_990_);
v___x_994_ = v___x_942_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v_a_959_ = v___x_994_;
goto v___jp_958_;
}
}
}
else
{
lean_object* v___x_998_; 
lean_dec_ref(v___x_983_);
lean_dec_ref(v_self_982_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_snd_953_);
lean_ctor_set(v___x_950_, 0, v_fst_952_);
v___x_998_ = v___x_950_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_snd_953_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_998_);
lean_ctor_set(v___x_942_, 0, v_fst_948_);
v___x_1000_ = v___x_942_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_948_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_a_959_ = v___x_1000_;
goto v___jp_958_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_fst_952_);
lean_del_object(v___x_950_);
lean_dec(v_fst_948_);
lean_dec(v_a_947_);
lean_del_object(v___x_942_);
lean_dec_ref(v_isTarget_928_);
lean_dec_ref(v_goal_927_);
v_a_1003_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_973_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_973_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_a_959_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_931_, v___x_962_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_927_, v_isTarget_928_, v_as_929_, v_sz_930_, v___x_963_, v___x_961_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_942_);
lean_dec(v_snd_940_);
lean_dec_ref(v_isTarget_928_);
lean_dec_ref(v_goal_927_);
v_a_1014_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_945_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_945_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
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
lean_dec_ref(v_goal_1038_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_b_1043_);
return v___x_1050_;
}
else
{
lean_object* v_snd_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1133_; 
v_snd_1051_ = lean_ctor_get(v_b_1043_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_b_1043_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_b_1043_, 0);
lean_dec(v_unused_1134_);
v___x_1053_ = v_b_1043_;
v_isShared_1054_ = v_isSharedCheck_1133_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snd_1051_);
lean_dec(v_b_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1133_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1055_ = lean_array_uget_borrowed(v_as_1040_, v_i_1042_);
lean_inc(v_a_1055_);
lean_inc_ref(v_goal_1038_);
v___x_1056_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1038_, v_a_1055_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_snd_1057_; lean_object* v_a_1058_; lean_object* v_fst_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1123_; 
v_snd_1057_ = lean_ctor_get(v_snd_1051_, 1);
lean_inc(v_snd_1057_);
v_a_1058_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1056_);
v_fst_1059_ = lean_ctor_get(v_snd_1051_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_snd_1051_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_snd_1051_, 1);
lean_dec(v_unused_1124_);
v___x_1061_ = v_snd_1051_;
v_isShared_1062_ = v_isSharedCheck_1123_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_fst_1059_);
lean_dec(v_snd_1051_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1123_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1122_; 
v_fst_1063_ = lean_ctor_get(v_snd_1057_, 0);
v_snd_1064_ = lean_ctor_get(v_snd_1057_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_snd_1057_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1066_ = v_snd_1057_;
v_isShared_1067_ = v_isSharedCheck_1122_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_snd_1057_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1122_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v_a_1070_; uint8_t v___x_1077_; 
v___x_1068_ = lean_box(0);
v___x_1077_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1058_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v_a_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_snd_1064_);
lean_ctor_set(v___x_1061_, 0, v_fst_1063_);
v___x_1079_ = v___x_1061_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_fst_1063_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_snd_1064_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1079_);
lean_ctor_set(v___x_1053_, 0, v_fst_1059_);
v___x_1081_ = v___x_1053_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v_a_1070_ = v___x_1081_;
goto v___jp_1069_;
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
lean_inc(v_a_1058_);
v___x_1084_ = lean_apply_6(v_isTarget_1039_, v_a_1058_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_a_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_snd_1064_);
lean_ctor_set(v___x_1061_, 0, v_fst_1063_);
v___x_1088_ = v___x_1061_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_fst_1063_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_snd_1064_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1088_);
lean_ctor_set(v___x_1053_, 0, v_fst_1059_);
v___x_1090_ = v___x_1053_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v_a_1070_ = v___x_1090_;
goto v___jp_1069_;
}
}
}
else
{
lean_object* v_self_1093_; lean_object* v___x_1094_; 
v_self_1093_ = lean_ctor_get(v_a_1058_, 0);
lean_inc_ref(v_self_1093_);
lean_dec(v_a_1058_);
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1064_, v_self_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_inc_ref(v_goal_1038_);
v___x_1095_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1038_, v_snd_1064_, v_self_1093_, v_fst_1063_, v_fst_1059_);
lean_inc(v___x_1095_);
v___x_1096_ = l_Rat_ofInt(v___x_1095_);
lean_inc_ref(v_goal_1038_);
v___x_1097_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1038_, v_self_1093_, v___x_1096_, v_snd_1064_);
v___x_1098_ = lean_box(0);
lean_inc(v___x_1095_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1063_, v___x_1095_, v___x_1098_);
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1101_ = lean_int_add(v___x_1095_, v___x_1100_);
lean_dec(v___x_1095_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1097_);
lean_ctor_set(v___x_1061_, 0, v___x_1099_);
v___x_1103_ = v___x_1061_;
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
v_a_1070_ = v___x_1105_;
goto v___jp_1069_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_self_1093_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_snd_1064_);
lean_ctor_set(v___x_1061_, 0, v_fst_1063_);
v___x_1109_ = v___x_1061_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_fst_1063_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_snd_1064_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1109_);
lean_ctor_set(v___x_1053_, 0, v_fst_1059_);
v___x_1111_ = v___x_1053_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1059_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v_a_1070_ = v___x_1111_;
goto v___jp_1069_;
}
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1066_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_del_object(v___x_1061_);
lean_dec(v_fst_1059_);
lean_dec(v_a_1058_);
lean_del_object(v___x_1053_);
lean_dec_ref(v_isTarget_1039_);
lean_dec_ref(v_goal_1038_);
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
v___jp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_a_1070_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_a_1070_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
size_t v___x_1073_; size_t v___x_1074_; 
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_add(v_i_1042_, v___x_1073_);
v_i_1042_ = v___x_1074_;
v_b_1043_ = v___x_1072_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_del_object(v___x_1053_);
lean_dec(v_snd_1051_);
lean_dec_ref(v_isTarget_1039_);
lean_dec_ref(v_goal_1038_);
v_a_1125_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1056_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1056_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1135_, lean_object* v_isTarget_1136_, lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1135_, v_isTarget_1136_, v_as_1137_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1149_, lean_object* v_isTarget_1150_, lean_object* v_as_1151_, size_t v_sz_1152_, size_t v_i_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_usize_dec_lt(v_i_1153_, v_sz_1152_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_isTarget_1150_);
lean_dec_ref(v_goal_1149_);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1154_);
return v___x_1161_;
}
else
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1244_; 
v_snd_1162_ = lean_ctor_get(v_b_1154_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_b_1154_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_b_1154_, 0);
lean_dec(v_unused_1245_);
v___x_1164_ = v_b_1154_;
v_isShared_1165_ = v_isSharedCheck_1244_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snd_1162_);
lean_dec(v_b_1154_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1244_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_a_1166_; lean_object* v___x_1167_; 
v_a_1166_ = lean_array_uget_borrowed(v_as_1151_, v_i_1153_);
lean_inc(v_a_1166_);
lean_inc_ref(v_goal_1149_);
v___x_1167_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1149_, v_a_1166_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_snd_1168_; lean_object* v_a_1169_; lean_object* v_fst_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1234_; 
v_snd_1168_ = lean_ctor_get(v_snd_1162_, 1);
lean_inc(v_snd_1168_);
v_a_1169_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1167_);
v_fst_1170_ = lean_ctor_get(v_snd_1162_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_snd_1162_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_snd_1162_, 1);
lean_dec(v_unused_1235_);
v___x_1172_ = v_snd_1162_;
v_isShared_1173_ = v_isSharedCheck_1234_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_fst_1170_);
lean_dec(v_snd_1162_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1234_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1233_; 
v_fst_1174_ = lean_ctor_get(v_snd_1168_, 0);
v_snd_1175_ = lean_ctor_get(v_snd_1168_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_snd_1168_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1177_ = v_snd_1168_;
v_isShared_1178_ = v_isSharedCheck_1233_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1175_);
lean_inc(v_fst_1174_);
lean_dec(v_snd_1168_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1233_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v_a_1181_; uint8_t v___x_1188_; 
v___x_1179_ = lean_box(0);
v___x_1188_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1169_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1190_; 
lean_dec(v_a_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_snd_1175_);
lean_ctor_set(v___x_1172_, 0, v_fst_1174_);
v___x_1190_ = v___x_1172_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_snd_1175_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1190_);
lean_ctor_set(v___x_1164_, 0, v_fst_1170_);
v___x_1192_ = v___x_1164_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v_a_1181_ = v___x_1192_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1195_; 
lean_inc_ref(v_isTarget_1150_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v_a_1169_);
v___x_1195_ = lean_apply_6(v_isTarget_1150_, v_a_1169_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, lean_box(0));
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; uint8_t v___x_1197_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = lean_unbox(v_a_1196_);
lean_dec(v_a_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v_a_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_snd_1175_);
lean_ctor_set(v___x_1172_, 0, v_fst_1174_);
v___x_1199_ = v___x_1172_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_snd_1175_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1199_);
lean_ctor_set(v___x_1164_, 0, v_fst_1170_);
v___x_1201_ = v___x_1164_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v_a_1181_ = v___x_1201_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v_self_1204_; lean_object* v___x_1205_; 
v_self_1204_ = lean_ctor_get(v_a_1169_, 0);
lean_inc_ref(v_self_1204_);
lean_dec(v_a_1169_);
v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1175_, v_self_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_inc_ref(v_goal_1149_);
v___x_1206_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1149_, v_snd_1175_, v_self_1204_, v_fst_1174_, v_fst_1170_);
lean_inc(v___x_1206_);
v___x_1207_ = l_Rat_ofInt(v___x_1206_);
lean_inc_ref(v_goal_1149_);
v___x_1208_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1149_, v_self_1204_, v___x_1207_, v_snd_1175_);
v___x_1209_ = lean_box(0);
lean_inc(v___x_1206_);
v___x_1210_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1174_, v___x_1206_, v___x_1209_);
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1212_ = lean_int_add(v___x_1206_, v___x_1211_);
lean_dec(v___x_1206_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v___x_1208_);
lean_ctor_set(v___x_1172_, 0, v___x_1210_);
v___x_1214_ = v___x_1172_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1208_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1214_);
lean_ctor_set(v___x_1164_, 0, v___x_1212_);
v___x_1216_ = v___x_1164_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v_a_1181_ = v___x_1216_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1220_; 
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_self_1204_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_snd_1175_);
lean_ctor_set(v___x_1172_, 0, v_fst_1174_);
v___x_1220_ = v___x_1172_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_snd_1175_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1220_);
lean_ctor_set(v___x_1164_, 0, v_fst_1170_);
v___x_1222_ = v___x_1164_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_fst_1170_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
v_a_1181_ = v___x_1222_;
goto v___jp_1180_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_del_object(v___x_1177_);
lean_dec(v_snd_1175_);
lean_dec(v_fst_1174_);
lean_del_object(v___x_1172_);
lean_dec(v_fst_1170_);
lean_dec(v_a_1169_);
lean_del_object(v___x_1164_);
lean_dec_ref(v_isTarget_1150_);
lean_dec_ref(v_goal_1149_);
v_a_1225_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1195_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1195_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
v___jp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_a_1181_);
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1183_ = v___x_1177_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_a_1181_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
size_t v___x_1184_; size_t v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1153_, v___x_1184_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1149_, v_isTarget_1150_, v_as_1151_, v_sz_1152_, v___x_1185_, v___x_1183_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_del_object(v___x_1164_);
lean_dec(v_snd_1162_);
lean_dec_ref(v_isTarget_1150_);
lean_dec_ref(v_goal_1149_);
v_a_1236_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1167_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1167_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1246_, lean_object* v_isTarget_1247_, lean_object* v_as_1248_, lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_b_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1246_, v_isTarget_1247_, v_as_1248_, v_sz_boxed_1257_, v_i_boxed_1258_, v_b_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v_as_1248_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_goal_1260_, lean_object* v_isTarget_1261_, lean_object* v_inh_1262_, lean_object* v_n_1263_, lean_object* v_b_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
if (lean_obj_tag(v_n_1263_) == 0)
{
lean_object* v_cs_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1304_; 
v_cs_1270_ = lean_ctor_get(v_n_1263_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_n_1263_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1272_ = v_n_1263_;
v_isShared_1273_ = v_isSharedCheck_1304_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_cs_1270_);
lean_dec(v_n_1263_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1304_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; size_t v_sz_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v_b_1264_);
v_sz_1276_ = lean_array_size(v_cs_1270_);
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_goal_1260_, v_isTarget_1261_, v_inh_1262_, v_cs_1270_, v_sz_1276_, v___x_1277_, v___x_1275_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec_ref(v_cs_1270_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1295_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1295_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_fst_1283_; 
v_fst_1283_ = lean_ctor_get(v_a_1279_, 0);
if (lean_obj_tag(v_fst_1283_) == 0)
{
lean_object* v_snd_1284_; lean_object* v___x_1286_; 
v_snd_1284_ = lean_ctor_get(v_a_1279_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_a_1279_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 1);
lean_ctor_set(v___x_1272_, 0, v_snd_1284_);
v___x_1286_ = v___x_1272_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_snd_1284_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1286_);
v___x_1288_ = v___x_1281_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_val_1291_; lean_object* v___x_1293_; 
lean_inc_ref(v_fst_1283_);
lean_dec(v_a_1279_);
lean_del_object(v___x_1272_);
v_val_1291_ = lean_ctor_get(v_fst_1283_, 0);
lean_inc(v_val_1291_);
lean_dec_ref(v_fst_1283_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_val_1291_);
v___x_1293_ = v___x_1281_;
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
lean_del_object(v___x_1272_);
v_a_1296_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1278_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1278_);
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
}
else
{
lean_object* v_vs_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1339_; 
v_vs_1305_ = lean_ctor_get(v_n_1263_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_n_1263_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1307_ = v_n_1263_;
v_isShared_1308_ = v_isSharedCheck_1339_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_vs_1305_);
lean_dec(v_n_1263_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1339_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v_b_1264_);
v_sz_1311_ = lean_array_size(v_vs_1305_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1260_, v_isTarget_1261_, v_vs_1305_, v_sz_1311_, v___x_1312_, v___x_1310_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec_ref(v_vs_1305_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1330_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_fst_1318_; 
v_fst_1318_ = lean_ctor_get(v_a_1314_, 0);
if (lean_obj_tag(v_fst_1318_) == 0)
{
lean_object* v_snd_1319_; lean_object* v___x_1321_; 
v_snd_1319_ = lean_ctor_get(v_a_1314_, 1);
lean_inc(v_snd_1319_);
lean_dec(v_a_1314_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v_snd_1319_);
v___x_1321_ = v___x_1307_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_snd_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1321_);
v___x_1323_ = v___x_1316_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_val_1326_; lean_object* v___x_1328_; 
lean_inc_ref(v_fst_1318_);
lean_dec(v_a_1314_);
lean_del_object(v___x_1307_);
v_val_1326_ = lean_ctor_get(v_fst_1318_, 0);
lean_inc(v_val_1326_);
lean_dec_ref(v_fst_1318_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_val_1326_);
v___x_1328_ = v___x_1316_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_val_1326_);
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
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_del_object(v___x_1307_);
v_a_1331_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1313_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1313_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_goal_1340_, lean_object* v_isTarget_1341_, lean_object* v_inh_1342_, lean_object* v_as_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec_ref(v_isTarget_1341_);
lean_dec_ref(v_goal_1340_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_b_1346_);
return v___x_1353_;
}
else
{
lean_object* v_snd_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1388_; 
v_snd_1354_ = lean_ctor_get(v_b_1346_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_b_1346_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_b_1346_, 0);
lean_dec(v_unused_1389_);
v___x_1356_ = v_b_1346_;
v_isShared_1357_ = v_isSharedCheck_1388_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_snd_1354_);
lean_dec(v_b_1346_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1388_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_array_uget_borrowed(v_as_1343_, v_i_1345_);
lean_inc(v_snd_1354_);
lean_inc(v_a_1358_);
lean_inc_ref(v_isTarget_1341_);
lean_inc_ref(v_goal_1340_);
v___x_1359_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_goal_1340_, v_isTarget_1341_, v_inh_1342_, v_a_1358_, v_snd_1354_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1379_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1379_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1379_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
if (lean_obj_tag(v_a_1360_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec_ref(v_isTarget_1341_);
lean_dec_ref(v_goal_1340_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1360_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1364_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_snd_1354_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1366_);
v___x_1368_ = v___x_1362_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_del_object(v___x_1362_);
lean_dec(v_snd_1354_);
v_a_1371_ = lean_ctor_get(v_a_1360_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v_a_1360_);
v___x_1372_ = lean_box(0);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_a_1371_);
lean_ctor_set(v___x_1356_, 0, v___x_1372_);
v___x_1374_ = v___x_1356_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_a_1371_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
size_t v___x_1375_; size_t v___x_1376_; 
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1345_, v___x_1375_);
v_i_1345_ = v___x_1376_;
v_b_1346_ = v___x_1374_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1356_);
lean_dec(v_snd_1354_);
lean_dec_ref(v_isTarget_1341_);
lean_dec_ref(v_goal_1340_);
v_a_1380_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1359_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1359_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_goal_1390_, lean_object* v_isTarget_1391_, lean_object* v_inh_1392_, lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_goal_1390_, v_isTarget_1391_, v_inh_1392_, v_as_1393_, v_sz_boxed_1402_, v_i_boxed_1403_, v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_as_1393_);
lean_dec_ref(v_inh_1392_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_goal_1405_, lean_object* v_isTarget_1406_, lean_object* v_inh_1407_, lean_object* v_n_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_goal_1405_, v_isTarget_1406_, v_inh_1407_, v_n_1408_, v_b_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec_ref(v_inh_1407_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1416_, lean_object* v_isTarget_1417_, lean_object* v_t_1418_, lean_object* v_init_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_root_1425_; lean_object* v_tail_1426_; lean_object* v___x_1427_; 
v_root_1425_ = lean_ctor_get(v_t_1418_, 0);
lean_inc_ref(v_root_1425_);
v_tail_1426_ = lean_ctor_get(v_t_1418_, 1);
lean_inc_ref(v_tail_1426_);
lean_dec_ref(v_t_1418_);
lean_inc_ref(v_init_1419_);
lean_inc_ref(v_isTarget_1417_);
lean_inc_ref(v_goal_1416_);
v___x_1427_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_goal_1416_, v_isTarget_1417_, v_init_1419_, v_root_1425_, v_init_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec_ref(v_init_1419_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1464_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1464_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1464_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; 
lean_dec_ref(v_tail_1426_);
lean_dec_ref(v_isTarget_1417_);
lean_dec_ref(v_goal_1416_);
v_a_1432_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v_a_1428_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_a_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; size_t v_sz_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
lean_del_object(v___x_1430_);
v_a_1436_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_a_1436_);
lean_dec_ref(v_a_1428_);
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v_a_1436_);
v_sz_1439_ = lean_array_size(v_tail_1426_);
v___x_1440_ = ((size_t)0ULL);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1416_, v_isTarget_1417_, v_tail_1426_, v_sz_1439_, v___x_1440_, v___x_1438_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec_ref(v_tail_1426_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1455_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1455_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_fst_1446_; 
v_fst_1446_ = lean_ctor_get(v_a_1442_, 0);
if (lean_obj_tag(v_fst_1446_) == 0)
{
lean_object* v_snd_1447_; lean_object* v___x_1449_; 
v_snd_1447_ = lean_ctor_get(v_a_1442_, 1);
lean_inc(v_snd_1447_);
lean_dec(v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_snd_1447_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_snd_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_val_1451_; lean_object* v___x_1453_; 
lean_inc_ref(v_fst_1446_);
lean_dec(v_a_1442_);
v_val_1451_ = lean_ctor_get(v_fst_1446_, 0);
lean_inc(v_val_1451_);
lean_dec_ref(v_fst_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_val_1451_);
v___x_1453_ = v___x_1444_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_val_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1441_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1441_);
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
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_tail_1426_);
lean_dec_ref(v_isTarget_1417_);
lean_dec_ref(v_goal_1416_);
v_a_1465_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1427_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1427_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1473_, lean_object* v_isTarget_1474_, lean_object* v_t_1475_, lean_object* v_init_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1473_, v_isTarget_1474_, v_t_1475_, v_init_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1483_, lean_object* v_a_1484_){
_start:
{
if (lean_obj_tag(v_a_1483_) == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_a_1484_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
else
{
lean_object* v_value_1488_; lean_object* v_tail_1489_; lean_object* v_num_1490_; lean_object* v_den_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_value_1488_ = lean_ctor_get(v_a_1483_, 1);
lean_inc(v_value_1488_);
v_tail_1489_ = lean_ctor_get(v_a_1483_, 2);
lean_inc(v_tail_1489_);
lean_dec_ref(v_a_1483_);
v_num_1490_ = lean_ctor_get(v_value_1488_, 0);
lean_inc(v_num_1490_);
v_den_1491_ = lean_ctor_get(v_value_1488_, 1);
lean_inc(v_den_1491_);
lean_dec(v_value_1488_);
v___x_1492_ = lean_unsigned_to_nat(1u);
v___x_1493_ = lean_nat_dec_eq(v_den_1491_, v___x_1492_);
lean_dec(v_den_1491_);
if (v___x_1493_ == 0)
{
lean_dec(v_num_1490_);
v_a_1483_ = v_tail_1489_;
goto _start;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1484_, v_num_1490_, v___x_1495_);
v_a_1483_ = v_tail_1489_;
v_a_1484_ = v___x_1496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1498_, v_a_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1502_, size_t v_sz_1503_, size_t v_i_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_usize_dec_lt(v_i_1504_, v_sz_1503_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_b_1505_);
return v___x_1512_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_array_uget_borrowed(v_as_1502_, v_i_1504_);
lean_inc(v_a_1513_);
v___x_1514_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1513_, v_b_1505_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1527_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1527_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
if (lean_obj_tag(v_a_1515_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v_a_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v_a_1519_);
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
else
{
lean_object* v_a_1523_; size_t v___x_1524_; size_t v___x_1525_; 
lean_del_object(v___x_1517_);
v_a_1523_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v_a_1515_);
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1504_, v___x_1524_);
v_i_1504_ = v___x_1525_;
v_b_1505_ = v_a_1523_;
goto _start;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1514_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1514_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1536_, lean_object* v_sz_1537_, lean_object* v_i_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1537_);
lean_dec(v_sz_1537_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1538_);
lean_dec(v_i_1538_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1536_, v_sz_boxed_1545_, v_i_boxed_1546_, v_b_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec_ref(v_as_1536_);
return v_res_1547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_unsigned_to_nat(16u);
v___x_1550_ = lean_mk_array(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_used_1553_; 
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1552_ = lean_unsigned_to_nat(0u);
v_used_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1553_, 0, v___x_1552_);
lean_ctor_set(v_used_1553_, 1, v___x_1551_);
return v_used_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1554_, lean_object* v_isTarget_1555_, lean_object* v_model_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_buckets_1562_; lean_object* v_used_1563_; size_t v_sz_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v_buckets_1562_ = lean_ctor_get(v_model_1556_, 1);
v_used_1563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1564_ = lean_array_size(v_buckets_1562_);
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1562_, v_sz_1564_, v___x_1565_, v_used_1563_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_toGoalState_1567_; lean_object* v_a_1568_; lean_object* v_exprs_1569_; lean_object* v_nextVal_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_toGoalState_1567_ = lean_ctor_get(v_goal_1554_, 0);
v_a_1568_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1566_);
v_exprs_1569_ = lean_ctor_get(v_toGoalState_1567_, 3);
lean_inc_ref(v_exprs_1569_);
v_nextVal_1570_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1568_);
lean_ctor_set(v___x_1571_, 1, v_model_1556_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_nextVal_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1554_, v_isTarget_1555_, v_exprs_1569_, v___x_1572_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1583_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_snd_1578_; lean_object* v_snd_1579_; lean_object* v___x_1581_; 
v_snd_1578_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_snd_1578_);
lean_dec(v_a_1574_);
v_snd_1579_ = lean_ctor_get(v_snd_1578_, 1);
lean_inc(v_snd_1579_);
lean_dec(v_snd_1578_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_snd_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_snd_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1573_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1573_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_model_1556_);
lean_dec_ref(v_isTarget_1555_);
lean_dec_ref(v_goal_1554_);
v_a_1592_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1566_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1566_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1600_, lean_object* v_isTarget_1601_, lean_object* v_model_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1600_, v_isTarget_1601_, v_model_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_a_1611_, lean_object* v_b_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1610_, v_a_1611_, v_b_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1614_, v_a_1615_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1622_, v_a_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1630_, lean_object* v_data_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1633_, lean_object* v_i_1634_, lean_object* v_source_1635_, lean_object* v_target_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1634_, v_source_1635_, v_target_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v_fst_1645_; lean_object* v_fst_1646_; lean_object* v_g_u2081_1647_; lean_object* v_g_u2082_1648_; uint8_t v___x_1649_; 
v_fst_1645_ = lean_ctor_get(v_x_1643_, 0);
v_fst_1646_ = lean_ctor_get(v_x_1644_, 0);
lean_inc_ref(v_goal_1642_);
v_g_u2081_1647_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1642_, v_fst_1645_);
v_g_u2082_1648_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1642_, v_fst_1646_);
v___x_1649_ = lean_nat_dec_eq(v_g_u2081_1647_, v_g_u2082_1648_);
if (v___x_1649_ == 0)
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_lt(v_g_u2081_1647_, v_g_u2082_1648_);
lean_dec(v_g_u2082_1648_);
lean_dec(v_g_u2081_1647_);
return v___x_1650_;
}
else
{
uint8_t v___x_1651_; 
lean_dec(v_g_u2082_1648_);
lean_dec(v_g_u2081_1647_);
v___x_1651_ = lean_expr_lt(v_fst_1645_, v_fst_1646_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1652_, v_x_1653_, v_x_1654_);
lean_dec_ref(v_x_1654_);
lean_dec_ref(v_x_1653_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1657_, lean_object* v_as_1658_, lean_object* v_lo_1659_, lean_object* v_hi_1660_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_lt(v_lo_1659_, v_hi_1660_);
if (v___x_1661_ == 0)
{
lean_dec(v_lo_1659_);
lean_dec_ref(v_goal_1657_);
return v_as_1658_;
}
else
{
lean_object* v___f_1662_; lean_object* v___x_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; uint8_t v___x_1666_; 
lean_inc_ref(v_goal_1657_);
v___f_1662_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1662_, 0, v_goal_1657_);
lean_inc(v_lo_1659_);
v___x_1663_ = l_Array_qpartition___redArg(v_as_1658_, v___f_1662_, v_lo_1659_, v_hi_1660_);
v_fst_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_fst_1664_);
v_snd_1665_ = lean_ctor_get(v___x_1663_, 1);
lean_inc(v_snd_1665_);
lean_dec_ref(v___x_1663_);
v___x_1666_ = lean_nat_dec_le(v_hi_1660_, v_fst_1664_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_inc_ref(v_goal_1657_);
v___x_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1657_, v_snd_1665_, v_lo_1659_, v_fst_1664_);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_fst_1664_, v___x_1668_);
lean_dec(v_fst_1664_);
v_as_1658_ = v___x_1667_;
v_lo_1659_ = v___x_1669_;
goto _start;
}
else
{
lean_dec(v_fst_1664_);
lean_dec(v_lo_1659_);
lean_dec_ref(v_goal_1657_);
return v_snd_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1671_, lean_object* v_as_1672_, lean_object* v_lo_1673_, lean_object* v_hi_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1671_, v_as_1672_, v_lo_1673_, v_hi_1674_);
lean_dec(v_hi_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1676_, lean_object* v_m_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = lean_array_get_size(v_m_1677_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_nat_dec_eq(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_sub(v___x_1678_, v___x_1681_);
v___x_1688_ = lean_nat_dec_le(v___x_1679_, v___x_1682_);
if (v___x_1688_ == 0)
{
lean_inc(v___x_1682_);
v___y_1684_ = v___x_1682_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v___x_1679_;
goto v___jp_1683_;
}
v___jp_1683_:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_nat_dec_le(v___y_1684_, v___x_1682_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_dec(v___x_1682_);
lean_inc(v___y_1684_);
v___x_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1676_, v_m_1677_, v___y_1684_, v___y_1684_);
lean_dec(v___y_1684_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1676_, v_m_1677_, v___y_1684_, v___x_1682_);
lean_dec(v___x_1682_);
return v___x_1687_;
}
}
}
else
{
lean_dec_ref(v_goal_1676_);
return v_m_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1689_, lean_object* v_n_1690_, lean_object* v_as_1691_, lean_object* v_lo_1692_, lean_object* v_hi_1693_, lean_object* v_w_1694_, lean_object* v_hlo_1695_, lean_object* v_hhi_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1689_, v_as_1691_, v_lo_1692_, v_hi_1693_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1698_, lean_object* v_n_1699_, lean_object* v_as_1700_, lean_object* v_lo_1701_, lean_object* v_hi_1702_, lean_object* v_w_1703_, lean_object* v_hlo_1704_, lean_object* v_hhi_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1698_, v_n_1699_, v_as_1700_, v_lo_1701_, v_hi_1702_, v_w_1703_, v_hlo_1704_, v_hhi_1705_);
lean_dec(v_hi_1702_);
lean_dec(v_n_1699_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
if (lean_obj_tag(v_a_1707_) == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1708_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v_key_1712_; lean_object* v_value_1713_; lean_object* v_tail_1714_; uint8_t v___x_1715_; 
v_key_1712_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_key_1712_);
v_value_1713_ = lean_ctor_get(v_a_1707_, 1);
lean_inc(v_value_1713_);
v_tail_1714_ = lean_ctor_get(v_a_1707_, 2);
lean_inc(v_tail_1714_);
lean_dec_ref(v_a_1707_);
lean_inc(v_key_1712_);
v___x_1715_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1712_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_key_1712_);
lean_ctor_set(v___x_1716_, 1, v_value_1713_);
v___x_1717_ = lean_array_push(v_a_1708_, v___x_1716_);
v_a_1707_ = v_tail_1714_;
v_a_1708_ = v___x_1717_;
goto _start;
}
else
{
lean_dec(v_value_1713_);
lean_dec(v_key_1712_);
v_a_1707_ = v_tail_1714_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1720_, v_a_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1724_, size_t v_sz_1725_, size_t v_i_1726_, lean_object* v_b_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_lt(v_i_1726_, v_sz_1725_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_b_1727_);
return v___x_1734_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_array_uget_borrowed(v_as_1724_, v_i_1726_);
lean_inc(v_a_1735_);
v___x_1736_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1735_, v_b_1727_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1749_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1749_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1749_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
if (lean_obj_tag(v_a_1737_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; 
v_a_1741_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v_a_1737_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_a_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
lean_object* v_a_1745_; size_t v___x_1746_; size_t v___x_1747_; 
lean_del_object(v___x_1739_);
v_a_1745_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_a_1745_);
lean_dec_ref(v_a_1737_);
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1726_, v___x_1746_);
v_i_1726_ = v___x_1747_;
v_b_1727_ = v_a_1745_;
goto _start;
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1736_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1736_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1758_, v_sz_boxed_1767_, v_i_boxed_1768_, v_b_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_as_1758_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1772_, lean_object* v_isTarget_1773_, lean_object* v_model_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___x_1780_; 
lean_inc_ref(v_goal_1772_);
v___x_1780_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1772_, v_isTarget_1773_, v_model_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_buckets_1782_; lean_object* v___x_1783_; size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v_buckets_1782_ = lean_ctor_get(v_a_1781_, 1);
lean_inc_ref(v_buckets_1782_);
lean_dec(v_a_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1784_ = lean_array_size(v_buckets_1782_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1782_, v_sz_1784_, v___x_1785_, v___x_1783_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec_ref(v_buckets_1782_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1772_, v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_dec_ref(v_goal_1772_);
return v___x_1786_;
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_goal_1772_);
v_a_1796_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1780_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1780_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1804_, lean_object* v_isTarget_1805_, lean_object* v_model_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1804_, v_isTarget_1805_, v_model_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1813_, v_a_1814_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1821_, v_a_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg(lean_object* v_cls_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_options_1835_; uint8_t v_hasTrace_1836_; 
v_options_1835_ = lean_ctor_get(v___y_1833_, 2);
v_hasTrace_1836_ = lean_ctor_get_uint8(v_options_1835_, sizeof(void*)*1);
if (v_hasTrace_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_cls_1832_);
v___x_1837_ = lean_box(v_hasTrace_1836_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v_inheritedTraceOptions_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_inheritedTraceOptions_1839_ = lean_ctor_get(v___y_1833_, 13);
v___x_1840_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___closed__1));
v___x_1841_ = l_Lean_Name_append(v___x_1840_, v_cls_1832_);
v___x_1842_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1839_, v_options_1835_, v___x_1841_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg___boxed(lean_object* v_cls_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg(v_cls_1845_, v___y_1846_);
lean_dec_ref(v___y_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg(v_cls_1849_, v___y_1852_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1(lean_object* v_msgData_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_env_1870_; lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v_lctx_1873_; lean_object* v_options_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1869_ = lean_st_ref_get(v___y_1867_);
v_env_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc_ref(v_env_1870_);
lean_dec(v___x_1869_);
v___x_1871_ = lean_st_ref_get(v___y_1865_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_mctx_1872_);
lean_dec(v___x_1871_);
v_lctx_1873_ = lean_ctor_get(v___y_1864_, 2);
v_options_1874_ = lean_ctor_get(v___y_1866_, 2);
lean_inc_ref(v_options_1874_);
lean_inc_ref(v_lctx_1873_);
v___x_1875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1875_, 0, v_env_1870_);
lean_ctor_set(v___x_1875_, 1, v_mctx_1872_);
lean_ctor_set(v___x_1875_, 2, v_lctx_1873_);
lean_ctor_set(v___x_1875_, 3, v_options_1874_);
v___x_1876_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_msgData_1863_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1___boxed(lean_object* v_msgData_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1(v_msgData_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1885_; double v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_float_of_nat(v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_cls_1890_, lean_object* v_msg_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_ref_1897_; lean_object* v___x_1898_; lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1943_; 
v_ref_1897_ = lean_ctor_get(v___y_1894_, 5);
v___x_1898_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1_spec__1(v_msg_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1943_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1943_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v_traceState_1904_; lean_object* v_env_1905_; lean_object* v_nextMacroScope_1906_; lean_object* v_ngen_1907_; lean_object* v_auxDeclNGen_1908_; lean_object* v_cache_1909_; lean_object* v_messages_1910_; lean_object* v_infoState_1911_; lean_object* v_snapshotTasks_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1942_; 
v___x_1903_ = lean_st_ref_take(v___y_1895_);
v_traceState_1904_ = lean_ctor_get(v___x_1903_, 4);
v_env_1905_ = lean_ctor_get(v___x_1903_, 0);
v_nextMacroScope_1906_ = lean_ctor_get(v___x_1903_, 1);
v_ngen_1907_ = lean_ctor_get(v___x_1903_, 2);
v_auxDeclNGen_1908_ = lean_ctor_get(v___x_1903_, 3);
v_cache_1909_ = lean_ctor_get(v___x_1903_, 5);
v_messages_1910_ = lean_ctor_get(v___x_1903_, 6);
v_infoState_1911_ = lean_ctor_get(v___x_1903_, 7);
v_snapshotTasks_1912_ = lean_ctor_get(v___x_1903_, 8);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1914_ = v___x_1903_;
v_isShared_1915_ = v_isSharedCheck_1942_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snapshotTasks_1912_);
lean_inc(v_infoState_1911_);
lean_inc(v_messages_1910_);
lean_inc(v_cache_1909_);
lean_inc(v_traceState_1904_);
lean_inc(v_auxDeclNGen_1908_);
lean_inc(v_ngen_1907_);
lean_inc(v_nextMacroScope_1906_);
lean_inc(v_env_1905_);
lean_dec(v___x_1903_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1942_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint64_t v_tid_1916_; lean_object* v_traces_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1941_; 
v_tid_1916_ = lean_ctor_get_uint64(v_traceState_1904_, sizeof(void*)*1);
v_traces_1917_ = lean_ctor_get(v_traceState_1904_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_traceState_1904_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1919_ = v_traceState_1904_;
v_isShared_1920_ = v_isSharedCheck_1941_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_traces_1917_);
lean_dec(v_traceState_1904_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1941_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; double v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0);
v___x_1923_ = 0;
v___x_1924_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1));
v___x_1925_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1925_, 0, v_cls_1890_);
lean_ctor_set(v___x_1925_, 1, v___x_1921_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
lean_ctor_set_float(v___x_1925_, sizeof(void*)*3, v___x_1922_);
lean_ctor_set_float(v___x_1925_, sizeof(void*)*3 + 8, v___x_1922_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*3 + 16, v___x_1923_);
v___x_1926_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_1927_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v_a_1899_);
lean_ctor_set(v___x_1927_, 2, v___x_1926_);
lean_inc(v_ref_1897_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_ref_1897_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Lean_PersistentArray_push___redArg(v_traces_1917_, v___x_1928_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1929_);
v___x_1931_ = v___x_1919_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1929_);
lean_ctor_set_uint64(v_reuseFailAlloc_1940_, sizeof(void*)*1, v_tid_1916_);
v___x_1931_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 4, v___x_1931_);
v___x_1933_ = v___x_1914_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_env_1905_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_nextMacroScope_1906_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_ngen_1907_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_auxDeclNGen_1908_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1939_, 5, v_cache_1909_);
lean_ctor_set(v_reuseFailAlloc_1939_, 6, v_messages_1910_);
lean_ctor_set(v_reuseFailAlloc_1939_, 7, v_infoState_1911_);
lean_ctor_set(v_reuseFailAlloc_1939_, 8, v_snapshotTasks_1912_);
v___x_1933_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1934_ = lean_st_ref_set(v___y_1895_, v___x_1933_);
v___x_1935_ = lean_box(0);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1935_);
v___x_1937_ = v___x_1901_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_cls_1944_, lean_object* v_msg_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_cls_1944_, v_msg_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__0));
v___x_1954_ = l_Lean_stringToMessageData(v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2(lean_object* v_traceClass_1956_, lean_object* v_as_1957_, size_t v_sz_1958_, size_t v_i_1959_, lean_object* v_b_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v_traceClass_1956_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1960_);
return v___x_1967_;
}
else
{
lean_object* v_a_1968_; lean_object* v_snd_1969_; lean_object* v_fst_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2005_; 
v_a_1968_ = lean_array_uget(v_as_1957_, v_i_1959_);
v_snd_1969_ = lean_ctor_get(v_a_1968_, 1);
v_fst_1970_ = lean_ctor_get(v_a_1968_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1972_ = v_a_1968_;
v_isShared_1973_ = v_isSharedCheck_2005_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1969_);
lean_inc(v_fst_1970_);
lean_dec(v_a_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2005_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_num_1974_; lean_object* v_den_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2004_; 
v_num_1974_ = lean_ctor_get(v_snd_1969_, 0);
v_den_1975_ = lean_ctor_get(v_snd_1969_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_snd_1969_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1977_ = v_snd_1969_;
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_den_1975_);
lean_inc(v_num_1974_);
lean_dec(v_snd_1969_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_1970_);
v___x_1981_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__1);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_1981_);
lean_ctor_set(v___x_1977_, 0, v___x_1980_);
v___x_1983_ = v___x_1977_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___y_1985_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_dec_eq(v_den_1975_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1997_ = l_Int_repr(v_num_1974_);
lean_dec(v_num_1974_);
v___x_1998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___closed__2));
v___x_1999_ = lean_string_append(v___x_1997_, v___x_1998_);
v___x_2000_ = l_Nat_reprFast(v_den_1975_);
v___x_2001_ = lean_string_append(v___x_1999_, v___x_2000_);
lean_dec_ref(v___x_2000_);
v___y_1985_ = v___x_2001_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_den_1975_);
v___x_2002_ = l_Int_repr(v_num_1974_);
lean_dec(v_num_1974_);
v___y_1985_ = v___x_2002_;
goto v___jp_1984_;
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___y_1985_);
v___x_1987_ = l_Lean_MessageData_ofFormat(v___x_1986_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 7);
lean_ctor_set(v___x_1972_, 1, v___x_1987_);
lean_ctor_set(v___x_1972_, 0, v___x_1983_);
v___x_1989_ = v___x_1972_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; 
lean_inc(v_traceClass_1956_);
v___x_1990_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_1956_, v___x_1989_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1990_) == 0)
{
size_t v___x_1991_; size_t v___x_1992_; 
lean_dec_ref(v___x_1990_);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_i_1959_, v___x_1991_);
v_i_1959_ = v___x_1992_;
v_b_1960_ = v___x_1979_;
goto _start;
}
else
{
lean_dec(v_traceClass_1956_);
return v___x_1990_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2___boxed(lean_object* v_traceClass_2006_, lean_object* v_as_2007_, lean_object* v_sz_2008_, lean_object* v_i_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2008_);
lean_dec(v_sz_2008_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2(v_traceClass_2006_, v_as_2007_, v_sz_boxed_2016_, v_i_boxed_2017_, v_b_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v_as_2007_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2019_, lean_object* v_model_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2048_; 
lean_inc(v_traceClass_2019_);
v___x_2026_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___redArg(v_traceClass_2019_, v_a_2023_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2048_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2048_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_dec(v_traceClass_2019_);
v___x_2032_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v___x_2036_; size_t v_sz_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_2029_);
v___x_2036_ = lean_box(0);
v_sz_2037_ = lean_array_size(v_model_2020_);
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__2(v_traceClass_2019_, v_model_2020_, v_sz_2037_, v___x_2038_, v___x_2036_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2047_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2036_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2036_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2049_, lean_object* v_model_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2049_, v_model_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec_ref(v_model_2050_);
return v_res_2056_;
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
