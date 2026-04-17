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
lean_dec_ref(v___x_114_);
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
lean_dec_ref(v___x_119_);
v___x_121_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v_goal_82_, v_arg_102_);
lean_dec_ref(v_arg_102_);
if (lean_obj_tag(v___x_121_) == 1)
{
lean_object* v_val_122_; uint8_t v___y_124_; uint8_t v___y_129_; uint8_t v___x_131_; 
v_val_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_val_122_);
lean_dec_ref(v___x_121_);
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
lean_object* v_k_x27_151_; uint8_t v___x_152_; 
v_k_x27_151_ = lean_array_fget_borrowed(v_keys_144_, v_i_146_);
v___x_152_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_147_, v_k_x27_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_i_146_, v___x_153_);
lean_dec(v_i_146_);
v_i_146_ = v___x_154_;
goto _start;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_array_fget_borrowed(v_vals_145_, v_i_146_);
lean_dec(v_i_146_);
lean_inc(v___x_156_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_158_, lean_object* v_vals_159_, lean_object* v_i_160_, lean_object* v_k_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_keys_158_, v_vals_159_, v_i_160_, v_k_161_);
lean_dec_ref(v_k_161_);
lean_dec_ref(v_vals_159_);
lean_dec_ref(v_keys_158_);
return v_res_162_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; 
v___x_163_ = ((size_t)5ULL);
v___x_164_ = ((size_t)1ULL);
v___x_165_ = lean_usize_shift_left(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; 
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__0);
v___x_168_ = lean_usize_sub(v___x_167_, v___x_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(lean_object* v_x_169_, size_t v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_es_172_; lean_object* v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; lean_object* v_j_177_; lean_object* v___x_178_; 
v_es_172_ = lean_ctor_get(v_x_169_, 0);
v___x_173_ = lean_box(2);
v___x_174_ = ((size_t)5ULL);
v___x_175_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___closed__1);
v___x_176_ = lean_usize_land(v_x_170_, v___x_175_);
v_j_177_ = lean_usize_to_nat(v___x_176_);
v___x_178_ = lean_array_get_borrowed(v___x_173_, v_es_172_, v_j_177_);
lean_dec(v_j_177_);
switch(lean_obj_tag(v___x_178_))
{
case 0:
{
lean_object* v_key_179_; lean_object* v_val_180_; uint8_t v___x_181_; 
v_key_179_ = lean_ctor_get(v___x_178_, 0);
v_val_180_ = lean_ctor_get(v___x_178_, 1);
v___x_181_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_171_, v_key_179_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
lean_inc(v_val_180_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_val_180_);
return v___x_183_;
}
}
case 1:
{
lean_object* v_node_184_; size_t v___x_185_; 
v_node_184_ = lean_ctor_get(v___x_178_, 0);
v___x_185_ = lean_usize_shift_right(v_x_170_, v___x_174_);
v_x_169_ = v_node_184_;
v_x_170_ = v___x_185_;
goto _start;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
return v___x_187_;
}
}
}
else
{
lean_object* v_ks_188_; lean_object* v_vs_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_ks_188_ = lean_ctor_get(v_x_169_, 0);
v_vs_189_ = lean_ctor_get(v_x_169_, 1);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0_spec__1___redArg(v_ks_188_, v_vs_189_, v___x_190_, v_x_171_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg___boxed(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
size_t v_x_2615__boxed_195_; lean_object* v_res_196_; 
v_x_2615__boxed_195_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_res_196_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_192_, v_x_2615__boxed_195_, v_x_194_);
lean_dec_ref(v_x_194_);
lean_dec_ref(v_x_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0___redArg(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint64_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0___redArg(v_x_197_, v___x_200_, v_x_198_);
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
lean_dec_ref(v___x_211_);
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
lean_dec_ref(v_fst_216_);
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
size_t v_x_2716__boxed_262_; lean_object* v_res_263_; 
v_x_2716__boxed_262_ = lean_unbox_usize(v_x_260_);
lean_dec(v_x_260_);
v_res_263_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_spec__0_spec__0(v_00_u03b2_258_, v_x_259_, v_x_2716__boxed_262_, v_x_261_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object* v_e_461_){
_start:
{
uint8_t v___y_463_; uint8_t v___x_498_; 
lean_inc_ref(v_e_461_);
v___x_498_ = l_Lean_Meta_Grind_Arith_isNatNum(v_e_461_);
if (v___x_498_ == 0)
{
uint8_t v___x_499_; 
lean_inc_ref(v_e_461_);
v___x_499_ = l_Lean_Meta_Grind_Arith_isIntNum(v_e_461_);
v___y_463_ = v___x_499_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_498_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__2));
v___x_465_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__5));
v___x_467_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__8));
v___x_469_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__11));
v___x_471_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__14));
v___x_473_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__17));
v___x_475_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__20));
v___x_477_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__23));
v___x_479_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__26));
v___x_481_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__29));
v___x_483_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__32));
v___x_485_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_Expr_isIte(v_e_461_);
if (v___x_486_ == 0)
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_Expr_isDIte(v_e_461_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__35));
v___x_489_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__40));
v___x_491_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__43));
v___x_493_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_isInterpretedTerm___closed__47));
v___x_495_ = l_Lean_Expr_isAppOf(v_e_461_, v___x_494_);
if (v___x_495_ == 0)
{
if (lean_obj_tag(v_e_461_) == 9)
{
lean_object* v_a_496_; 
v_a_496_ = lean_ctor_get(v_e_461_, 0);
lean_inc_ref(v_a_496_);
lean_dec_ref(v_e_461_);
if (lean_obj_tag(v_a_496_) == 0)
{
uint8_t v___x_497_; 
lean_dec_ref(v_a_496_);
v___x_497_ = 1;
return v___x_497_;
}
else
{
lean_dec_ref(v_a_496_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_493_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_491_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_489_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_486_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_485_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_483_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_481_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_479_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_477_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_475_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_473_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_471_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_469_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_467_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___x_465_;
}
}
else
{
lean_dec_ref(v_e_461_);
return v___y_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInterpretedTerm___boxed(lean_object* v_e_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_500_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
return v_x_503_;
}
else
{
lean_object* v_key_505_; lean_object* v_value_506_; lean_object* v_tail_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_530_; 
v_key_505_ = lean_ctor_get(v_x_504_, 0);
v_value_506_ = lean_ctor_get(v_x_504_, 1);
v_tail_507_ = lean_ctor_get(v_x_504_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_530_ == 0)
{
v___x_509_ = v_x_504_;
v_isShared_510_ = v_isSharedCheck_530_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_tail_507_);
lean_inc(v_value_506_);
lean_inc(v_key_505_);
lean_dec(v_x_504_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_530_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v_fold_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_511_ = lean_array_get_size(v_x_503_);
v___x_512_ = l_Lean_Expr_hash(v_key_505_);
v___x_513_ = 32ULL;
v___x_514_ = lean_uint64_shift_right(v___x_512_, v___x_513_);
v_fold_515_ = lean_uint64_xor(v___x_512_, v___x_514_);
v___x_516_ = 16ULL;
v___x_517_ = lean_uint64_shift_right(v_fold_515_, v___x_516_);
v___x_518_ = lean_uint64_xor(v_fold_515_, v___x_517_);
v___x_519_ = lean_uint64_to_usize(v___x_518_);
v___x_520_ = lean_usize_of_nat(v___x_511_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_sub(v___x_520_, v___x_521_);
v___x_523_ = lean_usize_land(v___x_519_, v___x_522_);
v___x_524_ = lean_array_uget_borrowed(v_x_503_, v___x_523_);
lean_inc(v___x_524_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 2, v___x_524_);
v___x_526_ = v___x_509_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_key_505_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_value_506_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v___x_524_);
v___x_526_ = v_reuseFailAlloc_529_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_array_uset(v_x_503_, v___x_523_, v___x_526_);
v_x_503_ = v___x_527_;
v_x_504_ = v_tail_507_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(lean_object* v_i_531_, lean_object* v_source_532_, lean_object* v_target_533_){
_start:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_array_get_size(v_source_532_);
v___x_535_ = lean_nat_dec_lt(v_i_531_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec_ref(v_source_532_);
lean_dec(v_i_531_);
return v_target_533_;
}
else
{
lean_object* v_es_536_; lean_object* v___x_537_; lean_object* v_source_538_; lean_object* v_target_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_es_536_ = lean_array_fget(v_source_532_, v_i_531_);
v___x_537_ = lean_box(0);
v_source_538_ = lean_array_fset(v_source_532_, v_i_531_, v___x_537_);
v_target_539_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_target_533_, v_es_536_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_i_531_, v___x_540_);
lean_dec(v_i_531_);
v_i_531_ = v___x_541_;
v_source_532_ = v_source_538_;
v_target_533_ = v_target_539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(lean_object* v_data_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_nbuckets_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_544_ = lean_array_get_size(v_data_543_);
v___x_545_ = lean_unsigned_to_nat(2u);
v_nbuckets_546_ = lean_nat_mul(v___x_544_, v___x_545_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_box(0);
v___x_549_ = lean_mk_array(v_nbuckets_546_, v___x_548_);
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v___x_547_, v_data_543_, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_dec(v_b_552_);
lean_dec_ref(v_a_551_);
return v_x_553_;
}
else
{
lean_object* v_key_554_; lean_object* v_value_555_; lean_object* v_tail_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_568_; 
v_key_554_ = lean_ctor_get(v_x_553_, 0);
v_value_555_ = lean_ctor_get(v_x_553_, 1);
v_tail_556_ = lean_ctor_get(v_x_553_, 2);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_568_ == 0)
{
v___x_558_ = v_x_553_;
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_tail_556_);
lean_inc(v_value_555_);
lean_inc(v_key_554_);
lean_dec(v_x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
uint8_t v___x_560_; 
v___x_560_ = lean_expr_eqv(v_key_554_, v_a_551_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_551_, v_b_552_, v_tail_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 2, v___x_561_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_key_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_value_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v_value_555_);
lean_dec(v_key_554_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_b_552_);
lean_ctor_set(v___x_558_, 0, v_a_551_);
v___x_566_ = v___x_558_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_551_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_b_552_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_tail_556_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(lean_object* v_a_569_, lean_object* v_x_570_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
uint8_t v___x_571_; 
v___x_571_ = 0;
return v___x_571_;
}
else
{
lean_object* v_key_572_; lean_object* v_tail_573_; uint8_t v___x_574_; 
v_key_572_ = lean_ctor_get(v_x_570_, 0);
v_tail_573_ = lean_ctor_get(v_x_570_, 2);
v___x_574_ = lean_expr_eqv(v_key_572_, v_a_569_);
if (v___x_574_ == 0)
{
v_x_570_ = v_tail_573_;
goto _start;
}
else
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg___boxed(lean_object* v_a_576_, lean_object* v_x_577_){
_start:
{
uint8_t v_res_578_; lean_object* v_r_579_; 
v_res_578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec_ref(v_a_576_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(lean_object* v_m_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_size_583_; lean_object* v_buckets_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_627_; 
v_size_583_ = lean_ctor_get(v_m_580_, 0);
v_buckets_584_ = lean_ctor_get(v_m_580_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_m_580_);
if (v_isSharedCheck_627_ == 0)
{
v___x_586_ = v_m_580_;
v_isShared_587_ = v_isSharedCheck_627_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_buckets_584_);
lean_inc(v_size_583_);
lean_dec(v_m_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_627_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; uint64_t v_fold_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v_bkt_601_; uint8_t v___x_602_; 
v___x_588_ = lean_array_get_size(v_buckets_584_);
v___x_589_ = l_Lean_Expr_hash(v_a_581_);
v___x_590_ = 32ULL;
v___x_591_ = lean_uint64_shift_right(v___x_589_, v___x_590_);
v_fold_592_ = lean_uint64_xor(v___x_589_, v___x_591_);
v___x_593_ = 16ULL;
v___x_594_ = lean_uint64_shift_right(v_fold_592_, v___x_593_);
v___x_595_ = lean_uint64_xor(v_fold_592_, v___x_594_);
v___x_596_ = lean_uint64_to_usize(v___x_595_);
v___x_597_ = lean_usize_of_nat(v___x_588_);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_sub(v___x_597_, v___x_598_);
v___x_600_ = lean_usize_land(v___x_596_, v___x_599_);
v_bkt_601_ = lean_array_uget_borrowed(v_buckets_584_, v___x_600_);
v___x_602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_581_, v_bkt_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v_size_x27_604_; lean_object* v___x_605_; lean_object* v_buckets_x27_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v_size_x27_604_ = lean_nat_add(v_size_583_, v___x_603_);
lean_dec(v_size_583_);
lean_inc(v_bkt_601_);
v___x_605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_605_, 0, v_a_581_);
lean_ctor_set(v___x_605_, 1, v_b_582_);
lean_ctor_set(v___x_605_, 2, v_bkt_601_);
v_buckets_x27_606_ = lean_array_uset(v_buckets_584_, v___x_600_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_nat_mul(v_size_x27_604_, v___x_607_);
v___x_609_ = lean_unsigned_to_nat(3u);
v___x_610_ = lean_nat_div(v___x_608_, v___x_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_array_get_size(v_buckets_x27_606_);
v___x_612_ = lean_nat_dec_le(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
if (v___x_612_ == 0)
{
lean_object* v_val_613_; lean_object* v___x_615_; 
v_val_613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_buckets_x27_606_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_val_613_);
lean_ctor_set(v___x_586_, 0, v_size_x27_604_);
v___x_615_ = v___x_586_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_size_x27_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_val_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v___x_618_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_buckets_x27_606_);
lean_ctor_set(v___x_586_, 0, v_size_x27_604_);
v___x_618_ = v___x_586_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_size_x27_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_buckets_x27_606_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v___x_620_; lean_object* v_buckets_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_inc(v_bkt_601_);
v___x_620_ = lean_box(0);
v_buckets_x27_621_ = lean_array_uset(v_buckets_584_, v___x_600_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_581_, v_b_582_, v_bkt_601_);
v___x_623_ = lean_array_uset(v_buckets_x27_621_, v___x_600_, v___x_622_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v___x_623_);
v___x_625_ = v___x_586_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_size_583_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(lean_object* v_v_628_, lean_object* v_as_x27_629_, lean_object* v_b_630_){
_start:
{
if (lean_obj_tag(v_as_x27_629_) == 0)
{
lean_dec_ref(v_v_628_);
return v_b_630_;
}
else
{
lean_object* v_head_631_; lean_object* v_tail_632_; lean_object* v___x_633_; 
v_head_631_ = lean_ctor_get(v_as_x27_629_, 0);
v_tail_632_ = lean_ctor_get(v_as_x27_629_, 1);
lean_inc_ref(v_v_628_);
lean_inc(v_head_631_);
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_b_630_, v_head_631_, v_v_628_);
v_as_x27_629_ = v_tail_632_;
v_b_630_ = v___x_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg___boxed(lean_object* v_v_635_, lean_object* v_as_x27_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_635_, v_as_x27_636_, v_b_637_);
lean_dec(v_as_x27_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc(lean_object* v_goal_639_, lean_object* v_e_640_, lean_object* v_v_641_, lean_object* v_a_642_){
_start:
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = 0;
v___x_644_ = l_Lean_Meta_Grind_Goal_getEqc(v_goal_639_, v_e_640_, v___x_643_);
v___x_645_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_641_, v___x_644_, v_a_642_);
lean_dec(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_assignEqc___boxed(lean_object* v_goal_646_, lean_object* v_e_647_, lean_object* v_v_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_646_, v_e_647_, v_v_648_, v_a_649_);
lean_dec_ref(v_goal_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0(lean_object* v_00_u03b2_651_, lean_object* v_m_652_, lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0___redArg(v_m_652_, v_a_653_, v_b_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(lean_object* v_v_656_, lean_object* v_as_657_, lean_object* v_as_x27_658_, lean_object* v_b_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___redArg(v_v_656_, v_as_x27_658_, v_b_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1___boxed(lean_object* v_v_662_, lean_object* v_as_663_, lean_object* v_as_x27_664_, lean_object* v_b_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_Arith_assignEqc_spec__1(v_v_662_, v_as_663_, v_as_x27_664_, v_b_665_, v_a_666_);
lean_dec(v_as_x27_664_);
lean_dec(v_as_663_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(lean_object* v_00_u03b2_668_, lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___redArg(v_a_669_, v_x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__0(v_00_u03b2_672_, v_a_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_a_673_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1(lean_object* v_00_u03b2_677_, lean_object* v_data_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1___redArg(v_data_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2(lean_object* v_00_u03b2_680_, lean_object* v_a_681_, lean_object* v_b_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__2___redArg(v_a_681_, v_b_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_685_, lean_object* v_i_686_, lean_object* v_source_687_, lean_object* v_target_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2___redArg(v_i_686_, v_source_687_, v_target_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_Arith_assignEqc_spec__0_spec__1_spec__2_spec__4___redArg(v_x_691_, v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
if (lean_obj_tag(v_x_695_) == 0)
{
return v_x_694_;
}
else
{
lean_object* v_key_696_; lean_object* v_value_697_; lean_object* v_tail_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_735_; 
v_key_696_ = lean_ctor_get(v_x_695_, 0);
v_value_697_ = lean_ctor_get(v_x_695_, 1);
v_tail_698_ = lean_ctor_get(v_x_695_, 2);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_695_);
if (v_isSharedCheck_735_ == 0)
{
v___x_700_ = v_x_695_;
v_isShared_701_ = v_isSharedCheck_735_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_tail_698_);
lean_inc(v_value_697_);
lean_inc(v_key_696_);
lean_dec(v_x_695_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_735_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint64_t v___y_704_; lean_object* v_intZero_722_; uint8_t v_isNeg_723_; 
v___x_702_ = lean_array_get_size(v_x_694_);
v_intZero_722_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_723_ = lean_int_dec_lt(v_key_696_, v_intZero_722_);
if (v_isNeg_723_ == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint64_t v___x_727_; 
v_a_724_ = lean_nat_abs(v_key_696_);
v___x_725_ = lean_unsigned_to_nat(2u);
v___x_726_ = lean_nat_mul(v___x_725_, v_a_724_);
lean_dec(v_a_724_);
v___x_727_ = lean_uint64_of_nat(v___x_726_);
lean_dec(v___x_726_);
v___y_704_ = v___x_727_;
goto v___jp_703_;
}
else
{
lean_object* v_abs_728_; lean_object* v_one_729_; lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint64_t v___x_734_; 
v_abs_728_ = lean_nat_abs(v_key_696_);
v_one_729_ = lean_unsigned_to_nat(1u);
v_a_730_ = lean_nat_sub(v_abs_728_, v_one_729_);
lean_dec(v_abs_728_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_nat_mul(v___x_731_, v_a_730_);
lean_dec(v_a_730_);
v___x_733_ = lean_nat_add(v___x_732_, v_one_729_);
lean_dec(v___x_732_);
v___x_734_ = lean_uint64_of_nat(v___x_733_);
lean_dec(v___x_733_);
v___y_704_ = v___x_734_;
goto v___jp_703_;
}
v___jp_703_:
{
uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v_fold_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_705_ = 32ULL;
v___x_706_ = lean_uint64_shift_right(v___y_704_, v___x_705_);
v_fold_707_ = lean_uint64_xor(v___y_704_, v___x_706_);
v___x_708_ = 16ULL;
v___x_709_ = lean_uint64_shift_right(v_fold_707_, v___x_708_);
v___x_710_ = lean_uint64_xor(v_fold_707_, v___x_709_);
v___x_711_ = lean_uint64_to_usize(v___x_710_);
v___x_712_ = lean_usize_of_nat(v___x_702_);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_sub(v___x_712_, v___x_713_);
v___x_715_ = lean_usize_land(v___x_711_, v___x_714_);
v___x_716_ = lean_array_uget_borrowed(v_x_694_, v___x_715_);
lean_inc(v___x_716_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 2, v___x_716_);
v___x_718_ = v___x_700_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_key_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_value_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_716_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = lean_array_uset(v_x_694_, v___x_715_, v___x_718_);
v_x_694_ = v___x_719_;
v_x_695_ = v_tail_698_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(lean_object* v_i_736_, lean_object* v_source_737_, lean_object* v_target_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_source_737_);
v___x_740_ = lean_nat_dec_lt(v_i_736_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v_source_737_);
lean_dec(v_i_736_);
return v_target_738_;
}
else
{
lean_object* v_es_741_; lean_object* v___x_742_; lean_object* v_source_743_; lean_object* v_target_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_es_741_ = lean_array_fget(v_source_737_, v_i_736_);
v___x_742_ = lean_box(0);
v_source_743_ = lean_array_fset(v_source_737_, v_i_736_, v___x_742_);
v_target_744_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_target_738_, v_es_741_);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_i_736_, v___x_745_);
lean_dec(v_i_736_);
v_i_736_ = v___x_746_;
v_source_737_ = v_source_743_;
v_target_738_ = v_target_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(lean_object* v_data_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_nbuckets_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_749_ = lean_array_get_size(v_data_748_);
v___x_750_ = lean_unsigned_to_nat(2u);
v_nbuckets_751_ = lean_nat_mul(v___x_749_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_box(0);
v___x_754_ = lean_mk_array(v_nbuckets_751_, v___x_753_);
v___x_755_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v___x_752_, v_data_748_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(lean_object* v_m_756_, lean_object* v_a_757_, lean_object* v_b_758_){
_start:
{
lean_object* v_size_759_; lean_object* v_buckets_760_; lean_object* v___x_761_; uint64_t v___y_763_; lean_object* v_intZero_800_; uint8_t v_isNeg_801_; 
v_size_759_ = lean_ctor_get(v_m_756_, 0);
v_buckets_760_ = lean_ctor_get(v_m_756_, 1);
v___x_761_ = lean_array_get_size(v_buckets_760_);
v_intZero_800_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v_isNeg_801_ = lean_int_dec_lt(v_a_757_, v_intZero_800_);
if (v_isNeg_801_ == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint64_t v___x_805_; 
v_a_802_ = lean_nat_abs(v_a_757_);
v___x_803_ = lean_unsigned_to_nat(2u);
v___x_804_ = lean_nat_mul(v___x_803_, v_a_802_);
lean_dec(v_a_802_);
v___x_805_ = lean_uint64_of_nat(v___x_804_);
lean_dec(v___x_804_);
v___y_763_ = v___x_805_;
goto v___jp_762_;
}
else
{
lean_object* v_abs_806_; lean_object* v_one_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint64_t v___x_812_; 
v_abs_806_ = lean_nat_abs(v_a_757_);
v_one_807_ = lean_unsigned_to_nat(1u);
v_a_808_ = lean_nat_sub(v_abs_806_, v_one_807_);
lean_dec(v_abs_806_);
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = lean_nat_mul(v___x_809_, v_a_808_);
lean_dec(v_a_808_);
v___x_811_ = lean_nat_add(v___x_810_, v_one_807_);
lean_dec(v___x_810_);
v___x_812_ = lean_uint64_of_nat(v___x_811_);
lean_dec(v___x_811_);
v___y_763_ = v___x_812_;
goto v___jp_762_;
}
v___jp_762_:
{
uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v_fold_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v_bkt_775_; uint8_t v___x_776_; 
v___x_764_ = 32ULL;
v___x_765_ = lean_uint64_shift_right(v___y_763_, v___x_764_);
v_fold_766_ = lean_uint64_xor(v___y_763_, v___x_765_);
v___x_767_ = 16ULL;
v___x_768_ = lean_uint64_shift_right(v_fold_766_, v___x_767_);
v___x_769_ = lean_uint64_xor(v_fold_766_, v___x_768_);
v___x_770_ = lean_uint64_to_usize(v___x_769_);
v___x_771_ = lean_usize_of_nat(v___x_761_);
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_sub(v___x_771_, v___x_772_);
v___x_774_ = lean_usize_land(v___x_770_, v___x_773_);
v_bkt_775_ = lean_array_uget_borrowed(v_buckets_760_, v___x_774_);
v___x_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0_spec__0___redArg(v_a_757_, v_bkt_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_797_; 
lean_inc_ref(v_buckets_760_);
lean_inc(v_size_759_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_m_756_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_798_ = lean_ctor_get(v_m_756_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_m_756_, 0);
lean_dec(v_unused_799_);
v___x_778_ = v_m_756_;
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_m_756_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v_size_x27_781_; lean_object* v___x_782_; lean_object* v_buckets_x27_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v_size_x27_781_ = lean_nat_add(v_size_759_, v___x_780_);
lean_dec(v_size_759_);
lean_inc(v_bkt_775_);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v_a_757_);
lean_ctor_set(v___x_782_, 1, v_b_758_);
lean_ctor_set(v___x_782_, 2, v_bkt_775_);
v_buckets_x27_783_ = lean_array_uset(v_buckets_760_, v___x_774_, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(4u);
v___x_785_ = lean_nat_mul(v_size_x27_781_, v___x_784_);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_div(v___x_785_, v___x_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_array_get_size(v_buckets_x27_783_);
v___x_789_ = lean_nat_dec_le(v___x_787_, v___x_788_);
lean_dec(v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v_val_790_; lean_object* v___x_792_; 
v_val_790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_buckets_x27_783_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_val_790_);
lean_ctor_set(v___x_778_, 0, v_size_x27_781_);
v___x_792_ = v___x_778_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_size_x27_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_val_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v___x_795_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_buckets_x27_783_);
lean_ctor_set(v___x_778_, 0, v_size_x27_781_);
v___x_795_ = v___x_778_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_size_x27_781_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_buckets_x27_783_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_dec(v_b_758_);
lean_dec(v_a_757_);
return v_m_756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(lean_object* v_goal_813_, lean_object* v_isTarget_814_, lean_object* v_as_815_, size_t v_sz_816_, size_t v_i_817_, lean_object* v_b_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_usize_dec_lt(v_i_817_, v_sz_816_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_isTarget_814_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v_b_818_);
return v___x_825_;
}
else
{
lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_908_; 
v_snd_826_ = lean_ctor_get(v_b_818_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_b_818_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_b_818_, 0);
lean_dec(v_unused_909_);
v___x_828_ = v_b_818_;
v_isShared_829_ = v_isSharedCheck_908_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_dec(v_b_818_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_908_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_array_uget_borrowed(v_as_815_, v_i_817_);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_813_, v_a_830_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_snd_832_; lean_object* v_a_833_; lean_object* v_fst_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_898_; 
v_snd_832_ = lean_ctor_get(v_snd_826_, 1);
lean_inc(v_snd_832_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_831_);
v_fst_834_ = lean_ctor_get(v_snd_826_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_snd_826_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_snd_826_, 1);
lean_dec(v_unused_899_);
v___x_836_ = v_snd_826_;
v_isShared_837_ = v_isSharedCheck_898_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_fst_834_);
lean_dec(v_snd_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_898_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_897_; 
v_fst_838_ = lean_ctor_get(v_snd_832_, 0);
v_snd_839_ = lean_ctor_get(v_snd_832_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_snd_832_);
if (v_isSharedCheck_897_ == 0)
{
v___x_841_ = v_snd_832_;
v_isShared_842_ = v_isSharedCheck_897_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v_snd_832_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_897_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v_a_845_; uint8_t v___x_852_; 
v___x_843_ = lean_box(0);
v___x_852_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_833_);
if (v___x_852_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_a_833_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_snd_839_);
lean_ctor_set(v___x_836_, 0, v_fst_838_);
v___x_854_ = v___x_836_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_snd_839_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_854_);
lean_ctor_set(v___x_828_, 0, v_fst_834_);
v___x_856_ = v___x_828_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v_a_845_ = v___x_856_;
goto v___jp_844_;
}
}
}
else
{
lean_object* v___x_859_; 
lean_inc_ref(v_isTarget_814_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v_a_833_);
v___x_859_ = lean_apply_6(v_isTarget_814_, v_a_833_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, lean_box(0));
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; uint8_t v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_861_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_863_; 
lean_dec(v_a_833_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_snd_839_);
lean_ctor_set(v___x_836_, 0, v_fst_838_);
v___x_863_ = v___x_836_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_snd_839_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_863_);
lean_ctor_set(v___x_828_, 0, v_fst_834_);
v___x_865_ = v___x_828_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v_a_845_ = v___x_865_;
goto v___jp_844_;
}
}
}
else
{
lean_object* v_self_868_; lean_object* v___x_869_; 
v_self_868_ = lean_ctor_get(v_a_833_, 0);
lean_inc_ref(v_self_868_);
lean_dec(v_a_833_);
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_839_, v_self_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_870_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_813_, v_snd_839_, v_self_868_, v_fst_838_, v_fst_834_);
lean_inc_n(v___x_870_, 2);
v___x_871_ = l_Rat_ofInt(v___x_870_);
v___x_872_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_813_, v_self_868_, v___x_871_, v_snd_839_);
v___x_873_ = lean_box(0);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_838_, v___x_870_, v___x_873_);
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_876_ = lean_int_add(v___x_870_, v___x_875_);
lean_dec(v___x_870_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_872_);
lean_ctor_set(v___x_836_, 0, v___x_874_);
v___x_878_ = v___x_836_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_872_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_878_);
lean_ctor_set(v___x_828_, 0, v___x_876_);
v___x_880_ = v___x_828_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
v_a_845_ = v___x_880_;
goto v___jp_844_;
}
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_869_);
lean_dec_ref(v_self_868_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_snd_839_);
lean_ctor_set(v___x_836_, 0, v_fst_838_);
v___x_884_ = v___x_836_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_snd_839_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_884_);
lean_ctor_set(v___x_828_, 0, v_fst_834_);
v___x_886_ = v___x_828_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v_a_845_ = v___x_886_;
goto v___jp_844_;
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_del_object(v___x_836_);
lean_dec(v_fst_834_);
lean_dec(v_a_833_);
lean_del_object(v___x_828_);
lean_dec_ref(v_isTarget_814_);
v_a_889_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_859_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_859_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_a_845_);
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_845_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
size_t v___x_848_; size_t v___x_849_; 
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_add(v_i_817_, v___x_848_);
v_i_817_ = v___x_849_;
v_b_818_ = v___x_847_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_828_);
lean_dec(v_snd_826_);
lean_dec_ref(v_isTarget_814_);
v_a_900_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_831_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_831_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9___boxed(lean_object* v_goal_910_, lean_object* v_isTarget_911_, lean_object* v_as_912_, lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
size_t v_sz_boxed_921_; size_t v_i_boxed_922_; lean_object* v_res_923_; 
v_sz_boxed_921_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_922_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_910_, v_isTarget_911_, v_as_912_, v_sz_boxed_921_, v_i_boxed_922_, v_b_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_as_912_);
lean_dec_ref(v_goal_910_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(lean_object* v_goal_924_, lean_object* v_isTarget_925_, lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v_isTarget_925_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_b_929_);
return v___x_936_;
}
else
{
lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1019_; 
v_snd_937_ = lean_ctor_get(v_b_929_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_b_929_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_b_929_, 0);
lean_dec(v_unused_1020_);
v___x_939_ = v_b_929_;
v_isShared_940_ = v_isSharedCheck_1019_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_dec(v_b_929_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1019_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_941_ = lean_array_uget_borrowed(v_as_926_, v_i_928_);
lean_inc(v_a_941_);
v___x_942_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_924_, v_a_941_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_snd_943_; lean_object* v_a_944_; lean_object* v_fst_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1009_; 
v_snd_943_ = lean_ctor_get(v_snd_937_, 1);
lean_inc(v_snd_943_);
v_a_944_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_944_);
lean_dec_ref(v___x_942_);
v_fst_945_ = lean_ctor_get(v_snd_937_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_snd_937_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_snd_937_, 1);
lean_dec(v_unused_1010_);
v___x_947_ = v_snd_937_;
v_isShared_948_ = v_isSharedCheck_1009_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_fst_945_);
lean_dec(v_snd_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1009_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fst_949_; lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1008_; 
v_fst_949_ = lean_ctor_get(v_snd_943_, 0);
v_snd_950_ = lean_ctor_get(v_snd_943_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_snd_943_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_952_ = v_snd_943_;
v_isShared_953_ = v_isSharedCheck_1008_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_inc(v_fst_949_);
lean_dec(v_snd_943_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1008_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v_a_956_; uint8_t v___x_963_; 
v___x_954_ = lean_box(0);
v___x_963_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_944_);
if (v___x_963_ == 0)
{
lean_object* v___x_965_; 
lean_dec(v_a_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_snd_950_);
lean_ctor_set(v___x_947_, 0, v_fst_949_);
v___x_965_ = v___x_947_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_949_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_snd_950_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_965_);
lean_ctor_set(v___x_939_, 0, v_fst_945_);
v___x_967_ = v___x_939_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_fst_945_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_956_ = v___x_967_;
goto v___jp_955_;
}
}
}
else
{
lean_object* v___x_970_; 
lean_inc_ref(v_isTarget_925_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v_a_944_);
v___x_970_ = lean_apply_6(v_isTarget_925_, v_a_944_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, lean_box(0));
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; uint8_t v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = lean_unbox(v_a_971_);
lean_dec(v_a_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v_a_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_snd_950_);
lean_ctor_set(v___x_947_, 0, v_fst_949_);
v___x_974_ = v___x_947_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_fst_949_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_snd_950_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_974_);
lean_ctor_set(v___x_939_, 0, v_fst_945_);
v___x_976_ = v___x_939_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_945_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
v_a_956_ = v___x_976_;
goto v___jp_955_;
}
}
}
else
{
lean_object* v_self_979_; lean_object* v___x_980_; 
v_self_979_ = lean_ctor_get(v_a_944_, 0);
lean_inc_ref(v_self_979_);
lean_dec(v_a_944_);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_950_, v_self_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_981_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_924_, v_snd_950_, v_self_979_, v_fst_949_, v_fst_945_);
lean_inc_n(v___x_981_, 2);
v___x_982_ = l_Rat_ofInt(v___x_981_);
v___x_983_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_924_, v_self_979_, v___x_982_, v_snd_950_);
v___x_984_ = lean_box(0);
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_949_, v___x_981_, v___x_984_);
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_987_ = lean_int_add(v___x_981_, v___x_986_);
lean_dec(v___x_981_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_983_);
lean_ctor_set(v___x_947_, 0, v___x_985_);
v___x_989_ = v___x_947_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_983_);
v___x_989_ = v_reuseFailAlloc_993_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_989_);
lean_ctor_set(v___x_939_, 0, v___x_987_);
v___x_991_ = v___x_939_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_a_956_ = v___x_991_;
goto v___jp_955_;
}
}
}
else
{
lean_object* v___x_995_; 
lean_dec_ref(v___x_980_);
lean_dec_ref(v_self_979_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_snd_950_);
lean_ctor_set(v___x_947_, 0, v_fst_949_);
v___x_995_ = v___x_947_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_fst_949_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_snd_950_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_995_);
lean_ctor_set(v___x_939_, 0, v_fst_945_);
v___x_997_ = v___x_939_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fst_945_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_a_956_ = v___x_997_;
goto v___jp_955_;
}
}
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
lean_dec(v_fst_949_);
lean_del_object(v___x_947_);
lean_dec(v_fst_945_);
lean_dec(v_a_944_);
lean_del_object(v___x_939_);
lean_dec_ref(v_isTarget_925_);
v_a_1000_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_970_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_970_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
v___jp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_a_956_);
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_958_ = v___x_952_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_a_956_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_add(v_i_928_, v___x_959_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5_spec__9(v_goal_924_, v_isTarget_925_, v_as_926_, v_sz_927_, v___x_960_, v___x_958_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_939_);
lean_dec(v_snd_937_);
lean_dec_ref(v_isTarget_925_);
v_a_1011_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_942_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_942_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5___boxed(lean_object* v_goal_1021_, lean_object* v_isTarget_1022_, lean_object* v_as_1023_, lean_object* v_sz_1024_, lean_object* v_i_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1024_);
lean_dec(v_sz_1024_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1021_, v_isTarget_1022_, v_as_1023_, v_sz_boxed_1032_, v_i_boxed_1033_, v_b_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec_ref(v_as_1023_);
lean_dec_ref(v_goal_1021_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(lean_object* v_goal_1035_, lean_object* v_isTarget_1036_, lean_object* v_as_1037_, size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_usize_dec_lt(v_i_1039_, v_sz_1038_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_isTarget_1036_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_b_1040_);
return v___x_1047_;
}
else
{
lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1130_; 
v_snd_1048_ = lean_ctor_get(v_b_1040_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_b_1040_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_b_1040_, 0);
lean_dec(v_unused_1131_);
v___x_1050_ = v_b_1040_;
v_isShared_1051_ = v_isSharedCheck_1130_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_dec(v_b_1040_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1130_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_array_uget_borrowed(v_as_1037_, v_i_1039_);
lean_inc(v_a_1052_);
v___x_1053_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1035_, v_a_1052_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_snd_1054_; lean_object* v_a_1055_; lean_object* v_fst_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1120_; 
v_snd_1054_ = lean_ctor_get(v_snd_1048_, 1);
lean_inc(v_snd_1054_);
v_a_1055_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1053_);
v_fst_1056_ = lean_ctor_get(v_snd_1048_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_snd_1048_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v_snd_1048_, 1);
lean_dec(v_unused_1121_);
v___x_1058_ = v_snd_1048_;
v_isShared_1059_ = v_isSharedCheck_1120_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_fst_1056_);
lean_dec(v_snd_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1120_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_fst_1060_; lean_object* v_snd_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1119_; 
v_fst_1060_ = lean_ctor_get(v_snd_1054_, 0);
v_snd_1061_ = lean_ctor_get(v_snd_1054_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_snd_1054_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1063_ = v_snd_1054_;
v_isShared_1064_ = v_isSharedCheck_1119_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_snd_1061_);
lean_inc(v_fst_1060_);
lean_dec(v_snd_1054_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1119_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v_a_1067_; uint8_t v___x_1074_; 
v___x_1065_ = lean_box(0);
v___x_1074_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1055_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_a_1055_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1076_ = v___x_1058_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_snd_1061_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1076_);
lean_ctor_set(v___x_1050_, 0, v_fst_1056_);
v___x_1078_ = v___x_1050_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_a_1067_ = v___x_1078_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v___x_1081_; 
lean_inc_ref(v_isTarget_1036_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v_a_1055_);
v___x_1081_ = lean_apply_6(v_isTarget_1036_, v_a_1055_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; uint8_t v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v___x_1081_);
v___x_1083_ = lean_unbox(v_a_1082_);
lean_dec(v_a_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_a_1055_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1085_ = v___x_1058_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_snd_1061_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1085_);
lean_ctor_set(v___x_1050_, 0, v_fst_1056_);
v___x_1087_ = v___x_1050_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v_a_1067_ = v___x_1087_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v_self_1090_; lean_object* v___x_1091_; 
v_self_1090_ = lean_ctor_get(v_a_1055_, 0);
lean_inc_ref(v_self_1090_);
lean_dec(v_a_1055_);
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1061_, v_self_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1092_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1035_, v_snd_1061_, v_self_1090_, v_fst_1060_, v_fst_1056_);
lean_inc_n(v___x_1092_, 2);
v___x_1093_ = l_Rat_ofInt(v___x_1092_);
v___x_1094_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1035_, v_self_1090_, v___x_1093_, v_snd_1061_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1060_, v___x_1092_, v___x_1095_);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1098_ = lean_int_add(v___x_1092_, v___x_1097_);
lean_dec(v___x_1092_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v___x_1094_);
lean_ctor_set(v___x_1058_, 0, v___x_1096_);
v___x_1100_ = v___x_1058_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1094_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1100_);
lean_ctor_set(v___x_1050_, 0, v___x_1098_);
v___x_1102_ = v___x_1050_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
v_a_1067_ = v___x_1102_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v___x_1106_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_self_1090_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_snd_1061_);
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1106_ = v___x_1058_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_fst_1060_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_snd_1061_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1106_);
lean_ctor_set(v___x_1050_, 0, v_fst_1056_);
v___x_1108_ = v___x_1050_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_fst_1056_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v_a_1067_ = v___x_1108_;
goto v___jp_1066_;
}
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1063_);
lean_dec(v_snd_1061_);
lean_dec(v_fst_1060_);
lean_del_object(v___x_1058_);
lean_dec(v_fst_1056_);
lean_dec(v_a_1055_);
lean_del_object(v___x_1050_);
lean_dec_ref(v_isTarget_1036_);
v_a_1111_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1081_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1081_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
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
v___x_1071_ = lean_usize_add(v_i_1039_, v___x_1070_);
v_i_1039_ = v___x_1071_;
v_b_1040_ = v___x_1069_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1050_);
lean_dec(v_snd_1048_);
lean_dec_ref(v_isTarget_1036_);
v_a_1122_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1053_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1053_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* v_goal_1132_, lean_object* v_isTarget_1133_, lean_object* v_as_1134_, lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
size_t v_sz_boxed_1143_; size_t v_i_boxed_1144_; lean_object* v_res_1145_; 
v_sz_boxed_1143_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1144_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1132_, v_isTarget_1133_, v_as_1134_, v_sz_boxed_1143_, v_i_boxed_1144_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_as_1134_);
lean_dec_ref(v_goal_1132_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(lean_object* v_goal_1146_, lean_object* v_isTarget_1147_, lean_object* v_as_1148_, size_t v_sz_1149_, size_t v_i_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_lt(v_i_1150_, v_sz_1149_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_dec_ref(v_isTarget_1147_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_b_1151_);
return v___x_1158_;
}
else
{
lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1241_; 
v_snd_1159_ = lean_ctor_get(v_b_1151_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_b_1151_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_b_1151_, 0);
lean_dec(v_unused_1242_);
v___x_1161_ = v_b_1151_;
v_isShared_1162_ = v_isSharedCheck_1241_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_dec(v_b_1151_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1241_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_array_uget_borrowed(v_as_1148_, v_i_1150_);
lean_inc(v_a_1163_);
v___x_1164_ = l_Lean_Meta_Grind_Goal_getENode(v_goal_1146_, v_a_1163_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_snd_1165_; lean_object* v_a_1166_; lean_object* v_fst_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1231_; 
v_snd_1165_ = lean_ctor_get(v_snd_1159_, 1);
lean_inc(v_snd_1165_);
v_a_1166_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1164_);
v_fst_1167_ = lean_ctor_get(v_snd_1159_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_snd_1159_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_snd_1159_, 1);
lean_dec(v_unused_1232_);
v___x_1169_ = v_snd_1159_;
v_isShared_1170_ = v_isSharedCheck_1231_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_fst_1167_);
lean_dec(v_snd_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1231_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1230_; 
v_fst_1171_ = lean_ctor_get(v_snd_1165_, 0);
v_snd_1172_ = lean_ctor_get(v_snd_1165_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_snd_1165_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1174_ = v_snd_1165_;
v_isShared_1175_ = v_isSharedCheck_1230_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_snd_1172_);
lean_inc(v_fst_1171_);
lean_dec(v_snd_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1230_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v_a_1178_; uint8_t v___x_1185_; 
v___x_1176_ = lean_box(0);
v___x_1185_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1166_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1187_; 
lean_dec(v_a_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_snd_1172_);
lean_ctor_set(v___x_1169_, 0, v_fst_1171_);
v___x_1187_ = v___x_1169_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1171_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1172_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1187_);
lean_ctor_set(v___x_1161_, 0, v_fst_1167_);
v___x_1189_ = v___x_1161_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_fst_1167_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_a_1178_ = v___x_1189_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v___x_1192_; 
lean_inc_ref(v_isTarget_1147_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
lean_inc(v___y_1153_);
lean_inc_ref(v___y_1152_);
lean_inc(v_a_1166_);
v___x_1192_ = lean_apply_6(v_isTarget_1147_, v_a_1166_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, lean_box(0));
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; uint8_t v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = lean_unbox(v_a_1193_);
lean_dec(v_a_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1196_; 
lean_dec(v_a_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_snd_1172_);
lean_ctor_set(v___x_1169_, 0, v_fst_1171_);
v___x_1196_ = v___x_1169_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_fst_1171_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_snd_1172_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1196_);
lean_ctor_set(v___x_1161_, 0, v_fst_1167_);
v___x_1198_ = v___x_1161_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_fst_1167_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
v_a_1178_ = v___x_1198_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v_self_1201_; lean_object* v___x_1202_; 
v_self_1201_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_self_1201_);
lean_dec(v_a_1166_);
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_satisfyDiseqs_checkDiseq_spec__0___redArg(v_snd_1172_, v_self_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1203_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go(v_goal_1146_, v_snd_1172_, v_self_1201_, v_fst_1171_, v_fst_1167_);
lean_inc_n(v___x_1203_, 2);
v___x_1204_ = l_Rat_ofInt(v___x_1203_);
v___x_1205_ = l_Lean_Meta_Grind_Arith_assignEqc(v_goal_1146_, v_self_1201_, v___x_1204_, v_snd_1172_);
v___x_1206_ = lean_box(0);
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_fst_1171_, v___x_1203_, v___x_1206_);
v___x_1208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go___closed__0);
v___x_1209_ = lean_int_add(v___x_1203_, v___x_1208_);
lean_dec(v___x_1203_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1205_);
lean_ctor_set(v___x_1169_, 0, v___x_1207_);
v___x_1211_ = v___x_1169_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1205_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1211_);
lean_ctor_set(v___x_1161_, 0, v___x_1209_);
v___x_1213_ = v___x_1161_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
v_a_1178_ = v___x_1213_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v___x_1217_; 
lean_dec_ref(v___x_1202_);
lean_dec_ref(v_self_1201_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_snd_1172_);
lean_ctor_set(v___x_1169_, 0, v_fst_1171_);
v___x_1217_ = v___x_1169_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_fst_1171_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_snd_1172_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1217_);
lean_ctor_set(v___x_1161_, 0, v_fst_1167_);
v___x_1219_ = v___x_1161_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_fst_1167_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_a_1178_ = v___x_1219_;
goto v___jp_1177_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_del_object(v___x_1174_);
lean_dec(v_snd_1172_);
lean_dec(v_fst_1171_);
lean_del_object(v___x_1169_);
lean_dec(v_fst_1167_);
lean_dec(v_a_1166_);
lean_del_object(v___x_1161_);
lean_dec_ref(v_isTarget_1147_);
v_a_1222_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1192_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1192_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_a_1178_);
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1180_ = v___x_1174_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_a_1178_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1150_, v___x_1181_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7_spec__9(v_goal_1146_, v_isTarget_1147_, v_as_1148_, v_sz_1149_, v___x_1182_, v___x_1180_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1183_;
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_del_object(v___x_1161_);
lean_dec(v_snd_1159_);
lean_dec_ref(v_isTarget_1147_);
v_a_1233_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1164_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1164_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7___boxed(lean_object* v_goal_1243_, lean_object* v_isTarget_1244_, lean_object* v_as_1245_, lean_object* v_sz_1246_, lean_object* v_i_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
size_t v_sz_boxed_1254_; size_t v_i_boxed_1255_; lean_object* v_res_1256_; 
v_sz_boxed_1254_ = lean_unbox_usize(v_sz_1246_);
lean_dec(v_sz_1246_);
v_i_boxed_1255_ = lean_unbox_usize(v_i_1247_);
lean_dec(v_i_1247_);
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1243_, v_isTarget_1244_, v_as_1245_, v_sz_boxed_1254_, v_i_boxed_1255_, v_b_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v_as_1245_);
lean_dec_ref(v_goal_1243_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(lean_object* v_init_1257_, lean_object* v_goal_1258_, lean_object* v_isTarget_1259_, lean_object* v_n_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
if (lean_obj_tag(v_n_1260_) == 0)
{
lean_object* v_cs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; size_t v_sz_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_cs_1267_ = lean_ctor_get(v_n_1260_, 0);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v_b_1261_);
v_sz_1270_ = lean_array_size(v_cs_1267_);
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1257_, v_goal_1258_, v_isTarget_1259_, v_cs_1267_, v_sz_1270_, v___x_1271_, v___x_1269_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1287_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_fst_1277_; 
v_fst_1277_ = lean_ctor_get(v_a_1273_, 0);
if (lean_obj_tag(v_fst_1277_) == 0)
{
lean_object* v_snd_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v_snd_1278_ = lean_ctor_get(v_a_1273_, 1);
lean_inc(v_snd_1278_);
lean_dec(v_a_1273_);
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_snd_1278_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1279_);
v___x_1281_ = v___x_1275_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; 
lean_inc_ref(v_fst_1277_);
lean_dec(v_a_1273_);
v_val_1283_ = lean_ctor_get(v_fst_1277_, 0);
lean_inc(v_val_1283_);
lean_dec_ref(v_fst_1277_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v_val_1283_);
v___x_1285_ = v___x_1275_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1272_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1272_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
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
lean_object* v_vs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_vs_1296_ = lean_ctor_get(v_n_1260_, 0);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v_b_1261_);
v_sz_1299_ = lean_array_size(v_vs_1296_);
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__7(v_goal_1258_, v_isTarget_1259_, v_vs_1296_, v_sz_1299_, v___x_1300_, v___x_1298_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1316_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1316_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1316_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_fst_1306_; 
v_fst_1306_ = lean_ctor_get(v_a_1302_, 0);
if (lean_obj_tag(v_fst_1306_) == 0)
{
lean_object* v_snd_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v_snd_1307_ = lean_ctor_get(v_a_1302_, 1);
lean_inc(v_snd_1307_);
lean_dec(v_a_1302_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_snd_1307_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1308_);
v___x_1310_ = v___x_1304_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
lean_object* v_val_1312_; lean_object* v___x_1314_; 
lean_inc_ref(v_fst_1306_);
lean_dec(v_a_1302_);
v_val_1312_ = lean_ctor_get(v_fst_1306_, 0);
lean_inc(v_val_1312_);
lean_dec_ref(v_fst_1306_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_val_1312_);
v___x_1314_ = v___x_1304_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_val_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1301_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1301_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(lean_object* v_init_1325_, lean_object* v_goal_1326_, lean_object* v_isTarget_1327_, lean_object* v_as_1328_, size_t v_sz_1329_, size_t v_i_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1330_, v_sz_1329_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_dec_ref(v_isTarget_1327_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_b_1331_);
return v___x_1338_;
}
else
{
lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1373_; 
v_snd_1339_ = lean_ctor_get(v_b_1331_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_b_1331_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_b_1331_, 0);
lean_dec(v_unused_1374_);
v___x_1341_ = v_b_1331_;
v_isShared_1342_ = v_isSharedCheck_1373_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_dec(v_b_1331_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1373_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_array_uget_borrowed(v_as_1328_, v_i_1330_);
lean_inc(v_snd_1339_);
lean_inc_ref(v_isTarget_1327_);
v___x_1344_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1325_, v_goal_1326_, v_isTarget_1327_, v_a_1343_, v_snd_1339_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1364_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
if (lean_obj_tag(v_a_1345_) == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_dec_ref(v_isTarget_1327_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1345_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1349_);
v___x_1351_ = v___x_1341_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_snd_1339_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1353_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1353_ = v___x_1347_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_del_object(v___x_1347_);
lean_dec(v_snd_1339_);
v_a_1356_ = lean_ctor_get(v_a_1345_, 0);
lean_inc(v_a_1356_);
lean_dec_ref(v_a_1345_);
v___x_1357_ = lean_box(0);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_a_1356_);
lean_ctor_set(v___x_1341_, 0, v___x_1357_);
v___x_1359_ = v___x_1341_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1356_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
size_t v___x_1360_; size_t v___x_1361_; 
v___x_1360_ = ((size_t)1ULL);
v___x_1361_ = lean_usize_add(v_i_1330_, v___x_1360_);
v_i_1330_ = v___x_1361_;
v_b_1331_ = v___x_1359_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1341_);
lean_dec(v_snd_1339_);
lean_dec_ref(v_isTarget_1327_);
v_a_1365_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1344_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1344_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6___boxed(lean_object* v_init_1375_, lean_object* v_goal_1376_, lean_object* v_isTarget_1377_, lean_object* v_as_1378_, lean_object* v_sz_1379_, lean_object* v_i_1380_, lean_object* v_b_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1379_);
lean_dec(v_sz_1379_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1380_);
lean_dec(v_i_1380_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4_spec__6(v_init_1375_, v_goal_1376_, v_isTarget_1377_, v_as_1378_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_as_1378_);
lean_dec_ref(v_goal_1376_);
lean_dec_ref(v_init_1375_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4___boxed(lean_object* v_init_1390_, lean_object* v_goal_1391_, lean_object* v_isTarget_1392_, lean_object* v_n_1393_, lean_object* v_b_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1390_, v_goal_1391_, v_isTarget_1392_, v_n_1393_, v_b_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec_ref(v_n_1393_);
lean_dec_ref(v_goal_1391_);
lean_dec_ref(v_init_1390_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(lean_object* v_goal_1401_, lean_object* v_isTarget_1402_, lean_object* v_t_1403_, lean_object* v_init_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_root_1410_; lean_object* v_tail_1411_; lean_object* v___x_1412_; 
v_root_1410_ = lean_ctor_get(v_t_1403_, 0);
v_tail_1411_ = lean_ctor_get(v_t_1403_, 1);
lean_inc_ref(v_isTarget_1402_);
lean_inc_ref(v_init_1404_);
v___x_1412_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__4(v_init_1404_, v_goal_1401_, v_isTarget_1402_, v_root_1410_, v_init_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec_ref(v_init_1404_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1449_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1449_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1449_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
if (lean_obj_tag(v_a_1413_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; 
lean_dec_ref(v_isTarget_1402_);
v_a_1417_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v_a_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v_a_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; size_t v_sz_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1415_);
v_a_1421_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v_a_1413_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
lean_ctor_set(v___x_1423_, 1, v_a_1421_);
v_sz_1424_ = lean_array_size(v_tail_1411_);
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3_spec__5(v_goal_1401_, v_isTarget_1402_, v_tail_1411_, v_sz_1424_, v___x_1425_, v___x_1423_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1440_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1440_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_fst_1431_; 
v_fst_1431_ = lean_ctor_get(v_a_1427_, 0);
if (lean_obj_tag(v_fst_1431_) == 0)
{
lean_object* v_snd_1432_; lean_object* v___x_1434_; 
v_snd_1432_ = lean_ctor_get(v_a_1427_, 1);
lean_inc(v_snd_1432_);
lean_dec(v_a_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_snd_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_snd_1432_);
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
lean_object* v_val_1436_; lean_object* v___x_1438_; 
lean_inc_ref(v_fst_1431_);
lean_dec(v_a_1427_);
v_val_1436_ = lean_ctor_get(v_fst_1431_, 0);
lean_inc(v_val_1436_);
lean_dec_ref(v_fst_1431_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_val_1436_);
v___x_1438_ = v___x_1429_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_val_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1426_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1426_);
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
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_isTarget_1402_);
v_a_1450_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1412_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1412_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3___boxed(lean_object* v_goal_1458_, lean_object* v_isTarget_1459_, lean_object* v_t_1460_, lean_object* v_init_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1458_, v_isTarget_1459_, v_t_1460_, v_init_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v_t_1460_);
lean_dec_ref(v_goal_1458_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
if (lean_obj_tag(v_a_1468_) == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1469_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v_value_1473_; lean_object* v_tail_1474_; lean_object* v_num_1475_; lean_object* v_den_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_value_1473_ = lean_ctor_get(v_a_1468_, 1);
lean_inc(v_value_1473_);
v_tail_1474_ = lean_ctor_get(v_a_1468_, 2);
lean_inc(v_tail_1474_);
lean_dec_ref(v_a_1468_);
v_num_1475_ = lean_ctor_get(v_value_1473_, 0);
lean_inc(v_num_1475_);
v_den_1476_ = lean_ctor_get(v_value_1473_, 1);
lean_inc(v_den_1476_);
lean_dec(v_value_1473_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_dec_eq(v_den_1476_, v___x_1477_);
lean_dec(v_den_1476_);
if (v___x_1478_ == 0)
{
lean_dec(v_num_1475_);
v_a_1468_ = v_tail_1474_;
goto _start;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_a_1469_, v_num_1475_, v___x_1480_);
v_a_1468_ = v_tail_1474_;
v_a_1469_ = v___x_1481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg___boxed(lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1483_, v_a_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1489_, v_sz_1488_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1490_);
return v___x_1497_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_array_uget_borrowed(v_as_1487_, v_i_1489_);
lean_inc(v_a_1498_);
v___x_1499_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1498_, v_b_1490_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1512_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1512_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1512_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
if (lean_obj_tag(v_a_1500_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; 
v_a_1504_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_a_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
else
{
lean_object* v_a_1508_; size_t v___x_1509_; size_t v___x_1510_; 
lean_del_object(v___x_1502_);
v_a_1508_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v_a_1500_);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_i_1489_, v___x_1509_);
v_i_1489_ = v___x_1510_;
v_b_1490_ = v_a_1508_;
goto _start;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1499_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1499_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2___boxed(lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_as_1521_, v_sz_boxed_1530_, v_i_boxed_1531_, v_b_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_as_1521_);
return v_res_1532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_unsigned_to_nat(16u);
v___x_1535_ = lean_mk_array(v___x_1534_, v___x_1533_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_used_1538_; 
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__0);
v___x_1537_ = lean_unsigned_to_nat(0u);
v_used_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_used_1538_, 0, v___x_1537_);
lean_ctor_set(v_used_1538_, 1, v___x_1536_);
return v_used_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(lean_object* v_goal_1539_, lean_object* v_isTarget_1540_, lean_object* v_model_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_buckets_1547_; lean_object* v_used_1548_; size_t v_sz_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_buckets_1547_ = lean_ctor_get(v_model_1541_, 1);
v_used_1548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___closed__1);
v_sz_1549_ = lean_array_size(v_buckets_1547_);
v___x_1550_ = ((size_t)0ULL);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__2(v_buckets_1547_, v_sz_1549_, v___x_1550_, v_used_1548_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_toGoalState_1552_; lean_object* v_a_1553_; lean_object* v_exprs_1554_; lean_object* v_nextVal_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_toGoalState_1552_ = lean_ctor_get(v_goal_1539_, 0);
v_a_1553_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1551_);
v_exprs_1554_ = lean_ctor_get(v_toGoalState_1552_, 2);
v_nextVal_1555_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_pickUnusedValue_go_spec__0___redArg___closed__0);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1553_);
lean_ctor_set(v___x_1556_, 1, v_model_1541_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_nextVal_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__3(v_goal_1539_, v_isTarget_1540_, v_exprs_1554_, v___x_1557_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1568_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1568_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_snd_1563_; lean_object* v_snd_1564_; lean_object* v___x_1566_; 
v_snd_1563_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_a_1559_);
v_snd_1564_ = lean_ctor_get(v_snd_1563_, 1);
lean_inc(v_snd_1564_);
lean_dec(v_snd_1563_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_snd_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_snd_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1558_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1558_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_model_1541_);
lean_dec_ref(v_isTarget_1540_);
v_a_1577_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1551_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1551_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned___boxed(lean_object* v_goal_1585_, lean_object* v_isTarget_1586_, lean_object* v_model_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1585_, v_isTarget_1586_, v_model_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec_ref(v_goal_1585_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0(lean_object* v_00_u03b2_1594_, lean_object* v_m_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0___redArg(v_m_1595_, v_a_1596_, v_b_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___redArg(v_a_1599_, v_a_1600_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1___boxed(lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__1(v_a_1607_, v_a_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0(lean_object* v_00_u03b2_1615_, lean_object* v_data_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0___redArg(v_data_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1618_, lean_object* v_i_1619_, lean_object* v_source_1620_, lean_object* v_target_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1___redArg(v_i_1619_, v_source_1620_, v_target_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1624_, v_x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(lean_object* v_goal_1627_, lean_object* v_hi_1628_, lean_object* v_pivot_1629_, lean_object* v_as_1630_, lean_object* v_i_1631_, lean_object* v_k_1632_){
_start:
{
uint8_t v___y_1634_; uint8_t v___x_1643_; 
v___x_1643_ = lean_nat_dec_lt(v_k_1632_, v_hi_1628_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_k_1632_);
v___x_1644_ = lean_array_fswap(v_as_1630_, v_i_1631_, v_hi_1628_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_i_1631_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; lean_object* v_fst_1647_; lean_object* v_fst_1648_; lean_object* v_g_u2081_1649_; lean_object* v_g_u2082_1650_; uint8_t v___x_1651_; 
v___x_1646_ = lean_array_fget_borrowed(v_as_1630_, v_k_1632_);
v_fst_1647_ = lean_ctor_get(v___x_1646_, 0);
v_fst_1648_ = lean_ctor_get(v_pivot_1629_, 0);
v_g_u2081_1649_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1627_, v_fst_1647_);
v_g_u2082_1650_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1627_, v_fst_1648_);
v___x_1651_ = lean_nat_dec_eq(v_g_u2081_1649_, v_g_u2082_1650_);
if (v___x_1651_ == 0)
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_nat_dec_lt(v_g_u2081_1649_, v_g_u2082_1650_);
lean_dec(v_g_u2082_1650_);
lean_dec(v_g_u2081_1649_);
v___y_1634_ = v___x_1652_;
goto v___jp_1633_;
}
else
{
uint8_t v___x_1653_; 
lean_dec(v_g_u2082_1650_);
lean_dec(v_g_u2081_1649_);
v___x_1653_ = lean_expr_lt(v_fst_1647_, v_fst_1648_);
v___y_1634_ = v___x_1653_;
goto v___jp_1633_;
}
}
v___jp_1633_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1u);
v___x_1636_ = lean_nat_add(v_k_1632_, v___x_1635_);
lean_dec(v_k_1632_);
v_k_1632_ = v___x_1636_;
goto _start;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_array_fswap(v_as_1630_, v_i_1631_, v_k_1632_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v_i_1631_, v___x_1639_);
lean_dec(v_i_1631_);
v___x_1641_ = lean_nat_add(v_k_1632_, v___x_1639_);
lean_dec(v_k_1632_);
v_as_1630_ = v___x_1638_;
v_i_1631_ = v___x_1640_;
v_k_1632_ = v___x_1641_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg___boxed(lean_object* v_goal_1654_, lean_object* v_hi_1655_, lean_object* v_pivot_1656_, lean_object* v_as_1657_, lean_object* v_i_1658_, lean_object* v_k_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1654_, v_hi_1655_, v_pivot_1656_, v_as_1657_, v_i_1658_, v_k_1659_);
lean_dec_ref(v_pivot_1656_);
lean_dec(v_hi_1655_);
lean_dec_ref(v_goal_1654_);
return v_res_1660_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(lean_object* v_goal_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v_fst_1664_; lean_object* v_fst_1665_; lean_object* v_g_u2081_1666_; lean_object* v_g_u2082_1667_; uint8_t v___x_1668_; 
v_fst_1664_ = lean_ctor_get(v_x_1662_, 0);
v_fst_1665_ = lean_ctor_get(v_x_1663_, 0);
v_g_u2081_1666_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1661_, v_fst_1664_);
v_g_u2082_1667_ = l_Lean_Meta_Grind_Goal_getGeneration(v_goal_1661_, v_fst_1665_);
v___x_1668_ = lean_nat_dec_eq(v_g_u2081_1666_, v_g_u2082_1667_);
if (v___x_1668_ == 0)
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_nat_dec_lt(v_g_u2081_1666_, v_g_u2082_1667_);
lean_dec(v_g_u2082_1667_);
lean_dec(v_g_u2081_1666_);
return v___x_1669_;
}
else
{
uint8_t v___x_1670_; 
lean_dec(v_g_u2082_1667_);
lean_dec(v_g_u2081_1666_);
v___x_1670_ = lean_expr_lt(v_fst_1664_, v_fst_1665_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0___boxed(lean_object* v_goal_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v_res_1674_; lean_object* v_r_1675_; 
v_res_1674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1671_, v_x_1672_, v_x_1673_);
lean_dec_ref(v_x_1673_);
lean_dec_ref(v_x_1672_);
lean_dec_ref(v_goal_1671_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(lean_object* v_goal_1676_, lean_object* v_n_1677_, lean_object* v_as_1678_, lean_object* v_lo_1679_, lean_object* v_hi_1680_){
_start:
{
lean_object* v___y_1682_; uint8_t v___x_1692_; 
v___x_1692_ = lean_nat_dec_lt(v_lo_1679_, v_hi_1680_);
if (v___x_1692_ == 0)
{
lean_dec(v_lo_1679_);
return v_as_1678_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_mid_1695_; lean_object* v___y_1697_; lean_object* v___y_1703_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1693_ = lean_nat_add(v_lo_1679_, v_hi_1680_);
v___x_1694_ = lean_unsigned_to_nat(1u);
v_mid_1695_ = lean_nat_shiftr(v___x_1693_, v___x_1694_);
lean_dec(v___x_1693_);
v___x_1708_ = lean_array_fget_borrowed(v_as_1678_, v_mid_1695_);
v___x_1709_ = lean_array_fget_borrowed(v_as_1678_, v_lo_1679_);
v___x_1710_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1676_, v___x_1708_, v___x_1709_);
if (v___x_1710_ == 0)
{
v___y_1703_ = v_as_1678_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_array_fswap(v_as_1678_, v_lo_1679_, v_mid_1695_);
v___y_1703_ = v___x_1711_;
goto v___jp_1702_;
}
v___jp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_array_fget_borrowed(v___y_1697_, v_mid_1695_);
v___x_1699_ = lean_array_fget_borrowed(v___y_1697_, v_hi_1680_);
v___x_1700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1676_, v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_dec(v_mid_1695_);
v___y_1682_ = v___y_1697_;
goto v___jp_1681_;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_array_fswap(v___y_1697_, v_mid_1695_, v_hi_1680_);
lean_dec(v_mid_1695_);
v___y_1682_ = v___x_1701_;
goto v___jp_1681_;
}
}
v___jp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_array_fget_borrowed(v___y_1703_, v_hi_1680_);
v___x_1705_ = lean_array_fget_borrowed(v___y_1703_, v_lo_1679_);
v___x_1706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___lam__0(v_goal_1676_, v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
v___y_1697_ = v___y_1703_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_array_fswap(v___y_1703_, v_lo_1679_, v_hi_1680_);
v___y_1697_ = v___x_1707_;
goto v___jp_1696_;
}
}
}
v___jp_1681_:
{
lean_object* v_pivot_1683_; lean_object* v___x_1684_; lean_object* v_fst_1685_; lean_object* v_snd_1686_; uint8_t v___x_1687_; 
v_pivot_1683_ = lean_array_fget(v___y_1682_, v_hi_1680_);
lean_inc_n(v_lo_1679_, 2);
v___x_1684_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1676_, v_hi_1680_, v_pivot_1683_, v___y_1682_, v_lo_1679_, v_lo_1679_);
lean_dec(v_pivot_1683_);
v_fst_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_fst_1685_);
v_snd_1686_ = lean_ctor_get(v___x_1684_, 1);
lean_inc(v_snd_1686_);
lean_dec_ref(v___x_1684_);
v___x_1687_ = lean_nat_dec_le(v_hi_1680_, v_fst_1685_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1676_, v_n_1677_, v_snd_1686_, v_lo_1679_, v_fst_1685_);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_add(v_fst_1685_, v___x_1689_);
lean_dec(v_fst_1685_);
v_as_1678_ = v___x_1688_;
v_lo_1679_ = v___x_1690_;
goto _start;
}
else
{
lean_dec(v_fst_1685_);
lean_dec(v_lo_1679_);
return v_snd_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg___boxed(lean_object* v_goal_1712_, lean_object* v_n_1713_, lean_object* v_as_1714_, lean_object* v_lo_1715_, lean_object* v_hi_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1712_, v_n_1713_, v_as_1714_, v_lo_1715_, v_hi_1716_);
lean_dec(v_hi_1716_);
lean_dec(v_n_1713_);
lean_dec_ref(v_goal_1712_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(lean_object* v_goal_1718_, lean_object* v_m_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1720_ = lean_array_get_size(v_m_1719_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_nat_dec_eq(v___x_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___y_1726_; uint8_t v___x_1730_; 
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_sub(v___x_1720_, v___x_1723_);
v___x_1730_ = lean_nat_dec_le(v___x_1721_, v___x_1724_);
if (v___x_1730_ == 0)
{
lean_inc(v___x_1724_);
v___y_1726_ = v___x_1724_;
goto v___jp_1725_;
}
else
{
v___y_1726_ = v___x_1721_;
goto v___jp_1725_;
}
v___jp_1725_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_nat_dec_le(v___y_1726_, v___x_1724_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
lean_dec(v___x_1724_);
lean_inc(v___y_1726_);
v___x_1728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1718_, v___x_1720_, v_m_1719_, v___y_1726_, v___y_1726_);
lean_dec(v___y_1726_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1718_, v___x_1720_, v_m_1719_, v___y_1726_, v___x_1724_);
lean_dec(v___x_1724_);
return v___x_1729_;
}
}
}
else
{
return v_m_1719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel___boxed(lean_object* v_goal_1731_, lean_object* v_m_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1731_, v_m_1732_);
lean_dec_ref(v_goal_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(lean_object* v_goal_1734_, lean_object* v_n_1735_, lean_object* v_as_1736_, lean_object* v_lo_1737_, lean_object* v_hi_1738_, lean_object* v_w_1739_, lean_object* v_hlo_1740_, lean_object* v_hhi_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___redArg(v_goal_1734_, v_n_1735_, v_as_1736_, v_lo_1737_, v_hi_1738_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0___boxed(lean_object* v_goal_1743_, lean_object* v_n_1744_, lean_object* v_as_1745_, lean_object* v_lo_1746_, lean_object* v_hi_1747_, lean_object* v_w_1748_, lean_object* v_hlo_1749_, lean_object* v_hhi_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0(v_goal_1743_, v_n_1744_, v_as_1745_, v_lo_1746_, v_hi_1747_, v_w_1748_, v_hlo_1749_, v_hhi_1750_);
lean_dec(v_hi_1747_);
lean_dec(v_n_1744_);
lean_dec_ref(v_goal_1743_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(lean_object* v_goal_1752_, lean_object* v_n_1753_, lean_object* v_lo_1754_, lean_object* v_hi_1755_, lean_object* v_hhi_1756_, lean_object* v_pivot_1757_, lean_object* v_as_1758_, lean_object* v_i_1759_, lean_object* v_k_1760_, lean_object* v_ilo_1761_, lean_object* v_ik_1762_, lean_object* v_w_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___redArg(v_goal_1752_, v_hi_1755_, v_pivot_1757_, v_as_1758_, v_i_1759_, v_k_1760_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0___boxed(lean_object* v_goal_1765_, lean_object* v_n_1766_, lean_object* v_lo_1767_, lean_object* v_hi_1768_, lean_object* v_hhi_1769_, lean_object* v_pivot_1770_, lean_object* v_as_1771_, lean_object* v_i_1772_, lean_object* v_k_1773_, lean_object* v_ilo_1774_, lean_object* v_ik_1775_, lean_object* v_w_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel_spec__0_spec__0(v_goal_1765_, v_n_1766_, v_lo_1767_, v_hi_1768_, v_hhi_1769_, v_pivot_1770_, v_as_1771_, v_i_1772_, v_k_1773_, v_ilo_1774_, v_ik_1775_, v_w_1776_);
lean_dec_ref(v_pivot_1770_);
lean_dec(v_hi_1768_);
lean_dec(v_lo_1767_);
lean_dec(v_n_1766_);
lean_dec_ref(v_goal_1765_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
if (lean_obj_tag(v_a_1778_) == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_a_1779_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
else
{
lean_object* v_key_1783_; lean_object* v_value_1784_; lean_object* v_tail_1785_; uint8_t v___x_1786_; 
v_key_1783_ = lean_ctor_get(v_a_1778_, 0);
lean_inc_n(v_key_1783_, 2);
v_value_1784_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_value_1784_);
v_tail_1785_ = lean_ctor_get(v_a_1778_, 2);
lean_inc(v_tail_1785_);
lean_dec_ref(v_a_1778_);
v___x_1786_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_key_1783_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_key_1783_);
lean_ctor_set(v___x_1787_, 1, v_value_1784_);
v___x_1788_ = lean_array_push(v_a_1779_, v___x_1787_);
v_a_1778_ = v_tail_1785_;
v_a_1779_ = v___x_1788_;
goto _start;
}
else
{
lean_dec(v_value_1784_);
lean_dec(v_key_1783_);
v_a_1778_ = v_tail_1785_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg___boxed(lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1791_, v_a_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(lean_object* v_as_1795_, size_t v_sz_1796_, size_t v_i_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_lt(v_i_1797_, v_sz_1796_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_b_1798_);
return v___x_1805_;
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_array_uget_borrowed(v_as_1795_, v_i_1797_);
lean_inc(v_a_1806_);
v___x_1807_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1806_, v_b_1798_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1820_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1820_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
if (lean_obj_tag(v_a_1808_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; 
v_a_1812_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v_a_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_a_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v_a_1816_; size_t v___x_1817_; size_t v___x_1818_; 
lean_del_object(v___x_1810_);
v_a_1816_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v_a_1808_);
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1797_, v___x_1817_);
v_i_1797_ = v___x_1818_;
v_b_1798_ = v_a_1816_;
goto _start;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1807_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1807_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1___boxed(lean_object* v_as_1829_, lean_object* v_sz_1830_, lean_object* v_i_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
size_t v_sz_boxed_1838_; size_t v_i_boxed_1839_; lean_object* v_res_1840_; 
v_sz_boxed_1838_ = lean_unbox_usize(v_sz_1830_);
lean_dec(v_sz_1830_);
v_i_boxed_1839_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_res_1840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_as_1829_, v_sz_boxed_1838_, v_i_boxed_1839_, v_b_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v_as_1829_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel(lean_object* v_goal_1843_, lean_object* v_isTarget_1844_, lean_object* v_model_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_assignUnassigned(v_goal_1843_, v_isTarget_1844_, v_model_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v_buckets_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v_buckets_1853_ = lean_ctor_get(v_a_1852_, 1);
lean_inc_ref(v_buckets_1853_);
lean_dec(v_a_1852_);
v___x_1854_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_finalizeModel___closed__0));
v_sz_1855_ = lean_array_size(v_buckets_1853_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__1(v_buckets_1853_, v_sz_1855_, v___x_1856_, v___x_1854_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec_ref(v_buckets_1853_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = l___private_Lean_Meta_Tactic_Grind_Arith_ModelUtil_0__Lean_Meta_Grind_Arith_sortModel(v_goal_1843_, v_a_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
return v___x_1857_;
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1851_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1851_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_finalizeModel___boxed(lean_object* v_goal_1875_, lean_object* v_isTarget_1876_, lean_object* v_model_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_Grind_Arith_finalizeModel(v_goal_1875_, v_isTarget_1876_, v_model_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec_ref(v_goal_1875_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___redArg(v_a_1884_, v_a_1885_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0___boxed(lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Grind_Arith_finalizeModel_spec__0(v_a_1892_, v_a_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(lean_object* v_msgData_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v_env_1907_; lean_object* v___x_1908_; lean_object* v_mctx_1909_; lean_object* v_lctx_1910_; lean_object* v_options_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1906_ = lean_st_ref_get(v___y_1904_);
v_env_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_env_1907_);
lean_dec(v___x_1906_);
v___x_1908_ = lean_st_ref_get(v___y_1902_);
v_mctx_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_ref(v_mctx_1909_);
lean_dec(v___x_1908_);
v_lctx_1910_ = lean_ctor_get(v___y_1901_, 2);
v_options_1911_ = lean_ctor_get(v___y_1903_, 2);
lean_inc_ref(v_options_1911_);
lean_inc_ref(v_lctx_1910_);
v___x_1912_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1912_, 0, v_env_1907_);
lean_ctor_set(v___x_1912_, 1, v_mctx_1909_);
lean_ctor_set(v___x_1912_, 2, v_lctx_1910_);
lean_ctor_set(v___x_1912_, 3, v_options_1911_);
v___x_1913_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v_msgData_1900_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0___boxed(lean_object* v_msgData_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msgData_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1921_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1922_; double v___x_1923_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_float_of_nat(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(lean_object* v_cls_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_ref_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1980_; 
v_ref_1934_ = lean_ctor_get(v___y_1931_, 5);
v___x_1935_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0_spec__0(v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1980_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1980_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v_traceState_1941_; lean_object* v_env_1942_; lean_object* v_nextMacroScope_1943_; lean_object* v_ngen_1944_; lean_object* v_auxDeclNGen_1945_; lean_object* v_cache_1946_; lean_object* v_messages_1947_; lean_object* v_infoState_1948_; lean_object* v_snapshotTasks_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1979_; 
v___x_1940_ = lean_st_ref_take(v___y_1932_);
v_traceState_1941_ = lean_ctor_get(v___x_1940_, 4);
v_env_1942_ = lean_ctor_get(v___x_1940_, 0);
v_nextMacroScope_1943_ = lean_ctor_get(v___x_1940_, 1);
v_ngen_1944_ = lean_ctor_get(v___x_1940_, 2);
v_auxDeclNGen_1945_ = lean_ctor_get(v___x_1940_, 3);
v_cache_1946_ = lean_ctor_get(v___x_1940_, 5);
v_messages_1947_ = lean_ctor_get(v___x_1940_, 6);
v_infoState_1948_ = lean_ctor_get(v___x_1940_, 7);
v_snapshotTasks_1949_ = lean_ctor_get(v___x_1940_, 8);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1951_ = v___x_1940_;
v_isShared_1952_ = v_isSharedCheck_1979_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snapshotTasks_1949_);
lean_inc(v_infoState_1948_);
lean_inc(v_messages_1947_);
lean_inc(v_cache_1946_);
lean_inc(v_traceState_1941_);
lean_inc(v_auxDeclNGen_1945_);
lean_inc(v_ngen_1944_);
lean_inc(v_nextMacroScope_1943_);
lean_inc(v_env_1942_);
lean_dec(v___x_1940_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1979_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
uint64_t v_tid_1953_; lean_object* v_traces_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1978_; 
v_tid_1953_ = lean_ctor_get_uint64(v_traceState_1941_, sizeof(void*)*1);
v_traces_1954_ = lean_ctor_get(v_traceState_1941_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_traceState_1941_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1956_ = v_traceState_1941_;
v_isShared_1957_ = v_isSharedCheck_1978_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_traces_1954_);
lean_dec(v_traceState_1941_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1978_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; double v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__0);
v___x_1960_ = 0;
v___x_1961_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__1));
v___x_1962_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1962_, 0, v_cls_1927_);
lean_ctor_set(v___x_1962_, 1, v___x_1958_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
lean_ctor_set_float(v___x_1962_, sizeof(void*)*3, v___x_1959_);
lean_ctor_set_float(v___x_1962_, sizeof(void*)*3 + 8, v___x_1959_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*3 + 16, v___x_1960_);
v___x_1963_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___closed__2));
v___x_1964_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v_a_1936_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
lean_inc(v_ref_1934_);
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_ref_1934_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Lean_PersistentArray_push___redArg(v_traces_1954_, v___x_1965_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1966_);
v___x_1968_ = v___x_1956_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1966_);
lean_ctor_set_uint64(v_reuseFailAlloc_1977_, sizeof(void*)*1, v_tid_1953_);
v___x_1968_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 4, v___x_1968_);
v___x_1970_ = v___x_1951_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_env_1942_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_nextMacroScope_1943_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_ngen_1944_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_auxDeclNGen_1945_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1976_, 5, v_cache_1946_);
lean_ctor_set(v_reuseFailAlloc_1976_, 6, v_messages_1947_);
lean_ctor_set(v_reuseFailAlloc_1976_, 7, v_infoState_1948_);
lean_ctor_set(v_reuseFailAlloc_1976_, 8, v_snapshotTasks_1949_);
v___x_1970_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1971_ = lean_st_ref_set(v___y_1932_, v___x_1970_);
v___x_1972_ = lean_box(0);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1972_);
v___x_1974_ = v___x_1938_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0___boxed(lean_object* v_cls_1981_, lean_object* v_msg_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_cls_1981_, v_msg_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1988_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__0));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(lean_object* v_traceClass_1993_, lean_object* v_as_1994_, size_t v_sz_1995_, size_t v_i_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_usize_dec_lt(v_i_1996_, v_sz_1995_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec(v_traceClass_1993_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_b_1997_);
return v___x_2004_;
}
else
{
lean_object* v_a_2005_; lean_object* v_snd_2006_; lean_object* v_fst_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2042_; 
v_a_2005_ = lean_array_uget(v_as_1994_, v_i_1996_);
v_snd_2006_ = lean_ctor_get(v_a_2005_, 1);
v_fst_2007_ = lean_ctor_get(v_a_2005_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2005_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2009_ = v_a_2005_;
v_isShared_2010_ = v_isSharedCheck_2042_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2006_);
lean_inc(v_fst_2007_);
lean_dec(v_a_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2042_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_num_2011_; lean_object* v_den_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2041_; 
v_num_2011_ = lean_ctor_get(v_snd_2006_, 0);
v_den_2012_ = lean_ctor_get(v_snd_2006_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_snd_2006_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2014_ = v_snd_2006_;
v_isShared_2015_ = v_isSharedCheck_2041_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_den_2012_);
lean_inc(v_num_2011_);
lean_dec(v_snd_2006_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2041_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_2007_);
v___x_2018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__1);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 7);
lean_ctor_set(v___x_2014_, 1, v___x_2018_);
lean_ctor_set(v___x_2014_, 0, v___x_2017_);
v___x_2020_ = v___x_2014_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___y_2022_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_dec_eq(v_den_2012_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2034_ = l_Int_repr(v_num_2011_);
lean_dec(v_num_2011_);
v___x_2035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___closed__2));
v___x_2036_ = lean_string_append(v___x_2034_, v___x_2035_);
v___x_2037_ = l_Nat_reprFast(v_den_2012_);
v___x_2038_ = lean_string_append(v___x_2036_, v___x_2037_);
lean_dec_ref(v___x_2037_);
v___y_2022_ = v___x_2038_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2039_; 
lean_dec(v_den_2012_);
v___x_2039_ = l_Int_repr(v_num_2011_);
lean_dec(v_num_2011_);
v___y_2022_ = v___x_2039_;
goto v___jp_2021_;
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2022_);
v___x_2024_ = l_Lean_MessageData_ofFormat(v___x_2023_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2024_);
lean_ctor_set(v___x_2009_, 0, v___x_2020_);
v___x_2026_ = v___x_2009_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; 
lean_inc(v_traceClass_1993_);
v___x_2027_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_traceModel_spec__0(v_traceClass_1993_, v___x_2026_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2027_) == 0)
{
size_t v___x_2028_; size_t v___x_2029_; 
lean_dec_ref(v___x_2027_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_1996_, v___x_2028_);
v_i_1996_ = v___x_2029_;
v_b_1997_ = v___x_2016_;
goto _start;
}
else
{
lean_dec(v_traceClass_1993_);
return v___x_2027_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1___boxed(lean_object* v_traceClass_2043_, lean_object* v_as_2044_, lean_object* v_sz_2045_, lean_object* v_i_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
size_t v_sz_boxed_2053_; size_t v_i_boxed_2054_; lean_object* v_res_2055_; 
v_sz_boxed_2053_ = lean_unbox_usize(v_sz_2045_);
lean_dec(v_sz_2045_);
v_i_boxed_2054_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2043_, v_as_2044_, v_sz_boxed_2053_, v_i_boxed_2054_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec_ref(v_as_2044_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel(lean_object* v_traceClass_2059_, lean_object* v_model_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_options_2069_; uint8_t v_hasTrace_2070_; 
v_options_2069_ = lean_ctor_get(v_a_2063_, 2);
v_hasTrace_2070_ = lean_ctor_get_uint8(v_options_2069_, sizeof(void*)*1);
if (v_hasTrace_2070_ == 0)
{
lean_dec(v_traceClass_2059_);
goto v___jp_2066_;
}
else
{
lean_object* v_inheritedTraceOptions_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_inheritedTraceOptions_2071_ = lean_ctor_get(v_a_2063_, 13);
v___x_2072_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_traceModel___closed__1));
lean_inc(v_traceClass_2059_);
v___x_2073_ = l_Lean_Name_append(v___x_2072_, v_traceClass_2059_);
v___x_2074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2071_, v_options_2069_, v___x_2073_);
lean_dec(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_traceClass_2059_);
goto v___jp_2066_;
}
else
{
lean_object* v___x_2075_; size_t v_sz_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2075_ = lean_box(0);
v_sz_2076_ = lean_array_size(v_model_2060_);
v___x_2077_ = ((size_t)0ULL);
v___x_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_traceModel_spec__1(v_traceClass_2059_, v_model_2060_, v_sz_2076_, v___x_2077_, v___x_2075_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2078_, 0);
lean_dec(v_unused_2086_);
v___x_2080_ = v___x_2078_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v___x_2078_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2075_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2075_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
return v___x_2078_;
}
}
}
v___jp_2066_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_traceModel___boxed(lean_object* v_traceClass_2087_, lean_object* v_model_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_Grind_Arith_traceModel(v_traceClass_2087_, v_model_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_model_2088_);
return v_res_2094_;
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
