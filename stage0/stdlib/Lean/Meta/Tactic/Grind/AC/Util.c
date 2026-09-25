// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Util
// Imports: public import Lean.Meta.Tactic.Grind.AC.Types public import Lean.Meta.Tactic.Grind.ProveEq public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Simp
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_expr_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`grind` internal error, invalid structure id"};
static const lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_AC_instMonadGetStructACM_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_AC_ACM_getStruct___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructACM = (const lean_object*)&l_Lean_Meta_Grind_AC_instMonadGetStructACM_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", neutral\?: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", idempotent: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ac"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(30, 146, 207, 37, 132, 85, 33, 194)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(243, 114, 160, 105, 78, 163, 71, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", comm: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Associative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(2, 251, 219, 24, 41, 141, 182, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Commutative"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(106, 96, 18, 51, 62, 235, 64, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "IdempotentOp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(245, 219, 239, 145, 216, 232, 46, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LawfulIdentity"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(50, 22, 200, 99, 71, 159, 239, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Meta_Grind_AC_acExt;
v___x_5_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_4_, v_a_1_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_6_, v_a_7_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27(lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_10_, v_a_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Meta_Grind_AC_get_x27(v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec(v_a_22_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg(lean_object* v_f_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_Lean_Meta_Grind_AC_acExt;
v___x_38_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_37_, v_f_34_, v_a_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(lean_object* v_f_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Meta_Grind_AC_modify_x27___redArg(v_f_39_, v_a_40_);
lean_dec(v_a_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27(lean_object* v_f_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = l_Lean_Meta_Grind_AC_acExt;
v___x_56_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_55_, v_f_43_, v_a_44_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___boxed(lean_object* v_f_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Grind_AC_modify_x27(v_f_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec(v_a_58_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_70_, v_a_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_71_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_88_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_88_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v_acSteps_81_; lean_object* v_steps_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v_acSteps_81_ = lean_ctor_get(v_a_77_, 9);
lean_inc(v_acSteps_81_);
lean_dec(v_a_77_);
v_steps_82_ = lean_ctor_get(v_a_75_, 3);
lean_inc(v_steps_82_);
lean_dec(v_a_75_);
v___x_83_ = lean_nat_dec_le(v_acSteps_81_, v_steps_82_);
lean_dec(v_steps_82_);
lean_dec(v_acSteps_81_);
v___x_84_ = lean_box(v___x_83_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_84_);
v___x_86_ = v___x_79_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_a_75_);
v_a_89_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_76_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_74_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_74_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_105_, v_a_106_, v_a_107_);
lean_dec_ref(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps(lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_110_, v_a_112_, v_a_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_Grind_AC_checkMaxSteps(v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
lean_dec(v_a_123_);
lean_dec(v_a_122_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(lean_object* v_s_134_){
_start:
{
lean_object* v_structs_135_; lean_object* v_opIdOf_136_; lean_object* v_exprToOpIds_137_; lean_object* v_steps_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_147_; 
v_structs_135_ = lean_ctor_get(v_s_134_, 0);
v_opIdOf_136_ = lean_ctor_get(v_s_134_, 1);
v_exprToOpIds_137_ = lean_ctor_get(v_s_134_, 2);
v_steps_138_ = lean_ctor_get(v_s_134_, 3);
v_isSharedCheck_147_ = !lean_is_exclusive(v_s_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_140_ = v_s_134_;
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_steps_138_);
lean_inc(v_exprToOpIds_137_);
lean_inc(v_opIdOf_136_);
lean_inc(v_structs_135_);
lean_dec(v_s_134_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_nat_add(v_steps_138_, v___x_142_);
lean_dec(v_steps_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 3, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_structs_135_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_opIdOf_136_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_exprToOpIds_137_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg(lean_object* v_a_149_){
_start:
{
lean_object* v___f_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___f_151_ = ((lean_object*)(l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0));
v___x_152_ = l_Lean_Meta_Grind_AC_acExt;
v___x_153_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_152_, v___f_151_, v_a_149_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_154_);
lean_dec(v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps(lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_157_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___boxed(lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_Grind_AC_incSteps(v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec(v_a_169_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(lean_object* v_inst_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_apply_2(v_inst_181_, lean_box(0), v_inst_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(lean_object* v_m_184_, lean_object* v_n_185_, lean_object* v_inst_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_apply_2(v_inst_186_, lean_box(0), v_inst_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg(lean_object* v_opId_189_, lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
lean_inc(v_a_200_);
lean_inc_ref(v_a_199_);
lean_inc(v_a_198_);
lean_inc_ref(v_a_197_);
lean_inc(v_a_196_);
lean_inc_ref(v_a_195_);
lean_inc(v_a_194_);
lean_inc_ref(v_a_193_);
lean_inc(v_a_192_);
lean_inc(v_a_191_);
v___x_202_ = lean_apply_12(v_x_190_, v_opId_189_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(lean_object* v_opId_203_, lean_object* v_x_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_Grind_AC_ACM_run___redArg(v_opId_203_, v_x_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec(v_a_205_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run(lean_object* v_00_u03b1_217_, lean_object* v_opId_218_, lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_221_);
lean_inc(v_a_220_);
v___x_231_ = lean_apply_12(v_x_219_, v_opId_218_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, lean_box(0));
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___boxed(lean_object* v_00_u03b1_232_, lean_object* v_opId_233_, lean_object* v_x_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Grind_AC_ACM_run(v_00_u03b1_232_, v_opId_233_, v_x_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg(lean_object* v_a_247_){
_start:
{
lean_object* v___x_249_; 
lean_inc(v_a_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_a_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_AC_getOpId___redArg(v_a_250_);
lean_dec(v_a_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; 
lean_inc(v_a_253_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v_a_253_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___boxed(lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_AC_getOpId(v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec(v_a_267_);
lean_dec(v_a_266_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v_env_286_; lean_object* v___x_287_; lean_object* v_toCold_288_; lean_object* v_mctx_289_; lean_object* v_lctx_290_; lean_object* v_options_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_285_ = lean_st_ref_get(v___y_283_);
v_env_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_env_286_);
lean_dec(v___x_285_);
v___x_287_ = lean_st_ref_get(v___y_281_);
v_toCold_288_ = lean_ctor_get(v___y_282_, 0);
v_mctx_289_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_mctx_289_);
lean_dec(v___x_287_);
v_lctx_290_ = lean_ctor_get(v___y_280_, 2);
v_options_291_ = lean_ctor_get(v_toCold_288_, 2);
lean_inc_ref(v_options_291_);
lean_inc_ref(v_lctx_290_);
v___x_292_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_292_, 0, v_env_286_);
lean_ctor_set(v___x_292_, 1, v_mctx_289_);
lean_ctor_set(v___x_292_, 2, v_lctx_290_);
lean_ctor_set(v___x_292_, 3, v_options_291_);
v___x_293_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_msgData_279_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_ref_308_; lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
v_ref_308_ = lean_ctor_get(v___y_305_, 2);
v___x_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
lean_inc(v_ref_308_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_ref_308_);
lean_ctor_set(v___x_314_, 1, v_a_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_330_, v_a_338_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_355_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_355_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_355_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_355_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_structs_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_structs_346_ = lean_ctor_get(v_a_342_, 0);
lean_inc_ref(v_structs_346_);
lean_dec(v_a_342_);
v___x_347_ = lean_array_get_size(v_structs_346_);
v___x_348_ = lean_nat_dec_lt(v_a_329_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v_structs_346_);
lean_del_object(v___x_344_);
v___x_349_ = lean_obj_once(&l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1, &l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1);
v___x_350_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v___x_349_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_array_fget(v_structs_346_, v_a_329_);
lean_dec_ref(v_structs_346_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_351_);
v___x_353_ = v___x_344_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_341_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_341_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_378_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_392_, lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(v_00_u03b1_392_, v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object* v_a_408_, lean_object* v_f_409_, lean_object* v_s_410_){
_start:
{
lean_object* v_structs_411_; lean_object* v_opIdOf_412_; lean_object* v_exprToOpIds_413_; lean_object* v_steps_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_structs_411_ = lean_ctor_get(v_s_410_, 0);
v_opIdOf_412_ = lean_ctor_get(v_s_410_, 1);
v_exprToOpIds_413_ = lean_ctor_get(v_s_410_, 2);
v_steps_414_ = lean_ctor_get(v_s_410_, 3);
v___x_415_ = lean_array_get_size(v_structs_411_);
v___x_416_ = lean_nat_dec_lt(v_a_408_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec_ref(v_f_409_);
return v_s_410_;
}
else
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_428_; 
lean_inc(v_steps_414_);
lean_inc_ref(v_exprToOpIds_413_);
lean_inc_ref(v_opIdOf_412_);
lean_inc_ref(v_structs_411_);
v_isSharedCheck_428_ = !lean_is_exclusive(v_s_410_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_429_ = lean_ctor_get(v_s_410_, 3);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_s_410_, 2);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_s_410_, 1);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_s_410_, 0);
lean_dec(v_unused_432_);
v___x_418_ = v_s_410_;
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
else
{
lean_dec(v_s_410_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_v_420_; lean_object* v___x_421_; lean_object* v_xs_x27_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v_v_420_ = lean_array_fget(v_structs_411_, v_a_408_);
v___x_421_ = lean_box(0);
v_xs_x27_422_ = lean_array_fset(v_structs_411_, v_a_408_, v___x_421_);
v___x_423_ = lean_apply_1(v_f_409_, v_v_420_);
v___x_424_ = lean_array_fset(v_xs_x27_422_, v_a_408_, v___x_423_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_424_);
v___x_426_ = v___x_418_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_opIdOf_412_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_exprToOpIds_413_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_steps_414_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_433_, lean_object* v_f_434_, lean_object* v_s_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(v_a_433_, v_f_434_, v_s_435_);
lean_dec(v_a_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object* v_f_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc(v_a_438_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_441_, 0, v_a_438_);
lean_closure_set(v___f_441_, 1, v_f_437_);
v___x_442_ = l_Lean_Meta_Grind_AC_acExt;
v___x_443_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_442_, v___f_441_, v_a_439_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object* v_f_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec(v_a_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object* v_f_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_449_, v_a_450_, v_a_451_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object* v_f_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Grind_AC_modifyStruct(v_f_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_op_494_; lean_object* v___x_496_; 
v_op_494_ = lean_ctor_get(v_a_490_, 3);
lean_inc_ref(v_op_494_);
lean_dec(v_a_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_op_494_);
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_op_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_a_499_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_489_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Grind_AC_getOp(v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
lean_dec(v_a_507_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
if (lean_obj_tag(v_x_521_) == 0)
{
return v_x_520_;
}
else
{
lean_object* v_key_522_; lean_object* v_value_523_; lean_object* v_tail_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_550_; 
v_key_522_ = lean_ctor_get(v_x_521_, 0);
v_value_523_ = lean_ctor_get(v_x_521_, 1);
v_tail_524_ = lean_ctor_get(v_x_521_, 2);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_550_ == 0)
{
v___x_526_ = v_x_521_;
v_isShared_527_ = v_isSharedCheck_550_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_tail_524_);
lean_inc(v_value_523_);
lean_inc(v_key_522_);
lean_dec(v_x_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_550_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; uint64_t v___y_530_; 
v___x_528_ = lean_array_get_size(v_x_520_);
if (lean_obj_tag(v_key_522_) == 0)
{
uint64_t v___x_548_; 
v___x_548_ = 1723ULL;
v___y_530_ = v___x_548_;
goto v___jp_529_;
}
else
{
uint64_t v_hash_549_; 
v_hash_549_ = lean_ctor_get_uint64(v_key_522_, sizeof(void*)*2);
v___y_530_ = v_hash_549_;
goto v___jp_529_;
}
v___jp_529_:
{
uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v_fold_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_531_ = 32ULL;
v___x_532_ = lean_uint64_shift_right(v___y_530_, v___x_531_);
v_fold_533_ = lean_uint64_xor(v___y_530_, v___x_532_);
v___x_534_ = 16ULL;
v___x_535_ = lean_uint64_shift_right(v_fold_533_, v___x_534_);
v___x_536_ = lean_uint64_xor(v_fold_533_, v___x_535_);
v___x_537_ = lean_uint64_to_usize(v___x_536_);
v___x_538_ = lean_usize_of_nat(v___x_528_);
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_sub(v___x_538_, v___x_539_);
v___x_541_ = lean_usize_land(v___x_537_, v___x_540_);
v___x_542_ = lean_array_uget_borrowed(v_x_520_, v___x_541_);
lean_inc(v___x_542_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_542_);
v___x_544_ = v___x_526_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_key_522_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_value_523_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v___x_542_);
v___x_544_ = v_reuseFailAlloc_547_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_array_uset(v_x_520_, v___x_541_, v___x_544_);
v_x_520_ = v___x_545_;
v_x_521_ = v_tail_524_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_551_, lean_object* v_source_552_, lean_object* v_target_553_){
_start:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v_source_552_);
v___x_555_ = lean_nat_dec_lt(v_i_551_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec_ref(v_source_552_);
lean_dec(v_i_551_);
return v_target_553_;
}
else
{
lean_object* v_es_556_; lean_object* v___x_557_; lean_object* v_source_558_; lean_object* v_target_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_es_556_ = lean_array_fget(v_source_552_, v_i_551_);
v___x_557_ = lean_box(0);
v_source_558_ = lean_array_fset(v_source_552_, v_i_551_, v___x_557_);
v_target_559_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_553_, v_es_556_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_i_551_, v___x_560_);
lean_dec(v_i_551_);
v_i_551_ = v___x_561_;
v_source_552_ = v_source_558_;
v_target_553_ = v_target_559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object* v_data_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_nbuckets_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_564_ = lean_array_get_size(v_data_563_);
v___x_565_ = lean_unsigned_to_nat(2u);
v_nbuckets_566_ = lean_nat_mul(v___x_564_, v___x_565_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_box(0);
v___x_569_ = lean_mk_array(v_nbuckets_566_, v___x_568_);
v___x_570_ = lean_array_propagate_mark(v_data_563_, v___x_569_);
v___x_571_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_567_, v_data_563_, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
uint8_t v___x_574_; 
v___x_574_ = 0;
return v___x_574_;
}
else
{
lean_object* v_key_575_; lean_object* v_tail_576_; uint8_t v___x_577_; 
v_key_575_ = lean_ctor_get(v_x_573_, 0);
v_tail_576_ = lean_ctor_get(v_x_573_, 2);
v___x_577_ = lean_name_eq(v_key_575_, v_a_572_);
if (v___x_577_ == 0)
{
v_x_573_ = v_tail_576_;
goto _start;
}
else
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
uint8_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_579_, v_x_580_);
lean_dec(v_x_580_);
lean_dec(v_a_579_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object* v_m_583_, lean_object* v_a_584_, lean_object* v_b_585_){
_start:
{
lean_object* v_size_586_; lean_object* v_buckets_587_; lean_object* v___x_588_; uint64_t v___y_590_; 
v_size_586_ = lean_ctor_get(v_m_583_, 0);
v_buckets_587_ = lean_ctor_get(v_m_583_, 1);
v___x_588_ = lean_array_get_size(v_buckets_587_);
if (lean_obj_tag(v_a_584_) == 0)
{
uint64_t v___x_627_; 
v___x_627_ = 1723ULL;
v___y_590_ = v___x_627_;
goto v___jp_589_;
}
else
{
uint64_t v_hash_628_; 
v_hash_628_ = lean_ctor_get_uint64(v_a_584_, sizeof(void*)*2);
v___y_590_ = v_hash_628_;
goto v___jp_589_;
}
v___jp_589_:
{
uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v_fold_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v_bkt_602_; uint8_t v___x_603_; 
v___x_591_ = 32ULL;
v___x_592_ = lean_uint64_shift_right(v___y_590_, v___x_591_);
v_fold_593_ = lean_uint64_xor(v___y_590_, v___x_592_);
v___x_594_ = 16ULL;
v___x_595_ = lean_uint64_shift_right(v_fold_593_, v___x_594_);
v___x_596_ = lean_uint64_xor(v_fold_593_, v___x_595_);
v___x_597_ = lean_uint64_to_usize(v___x_596_);
v___x_598_ = lean_usize_of_nat(v___x_588_);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_sub(v___x_598_, v___x_599_);
v___x_601_ = lean_usize_land(v___x_597_, v___x_600_);
v_bkt_602_ = lean_array_uget_borrowed(v_buckets_587_, v___x_601_);
v___x_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_584_, v_bkt_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_624_; 
lean_inc_ref(v_buckets_587_);
lean_inc(v_size_586_);
v_isSharedCheck_624_ = !lean_is_exclusive(v_m_583_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_625_ = lean_ctor_get(v_m_583_, 1);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_m_583_, 0);
lean_dec(v_unused_626_);
v___x_605_ = v_m_583_;
v_isShared_606_ = v_isSharedCheck_624_;
goto v_resetjp_604_;
}
else
{
lean_dec(v_m_583_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_624_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v_size_x27_608_; lean_object* v___x_609_; lean_object* v_buckets_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_607_ = lean_unsigned_to_nat(1u);
v_size_x27_608_ = lean_nat_add(v_size_586_, v___x_607_);
lean_dec(v_size_586_);
lean_inc(v_bkt_602_);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v_a_584_);
lean_ctor_set(v___x_609_, 1, v_b_585_);
lean_ctor_set(v___x_609_, 2, v_bkt_602_);
v_buckets_x27_610_ = lean_array_uset(v_buckets_587_, v___x_601_, v___x_609_);
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
v_val_617_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_buckets_x27_610_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v_val_617_);
lean_ctor_set(v___x_605_, 0, v_size_x27_608_);
v___x_619_ = v___x_605_;
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
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v_buckets_x27_610_);
lean_ctor_set(v___x_605_, 0, v_size_x27_608_);
v___x_622_ = v___x_605_;
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
}
else
{
lean_dec(v_b_585_);
lean_dec(v_a_584_);
return v_m_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object* v_as_x27_629_, lean_object* v_b_630_){
_start:
{
if (lean_obj_tag(v_as_x27_629_) == 0)
{
return v_b_630_;
}
else
{
lean_object* v_head_631_; lean_object* v_tail_632_; lean_object* v___x_633_; lean_object* v_r_634_; 
v_head_631_ = lean_ctor_get(v_as_x27_629_, 0);
v_tail_632_ = lean_ctor_get(v_as_x27_629_, 1);
v___x_633_ = lean_box(0);
lean_inc(v_head_631_);
v_r_634_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_630_, v_head_631_, v___x_633_);
v_as_x27_629_ = v_tail_632_;
v_b_630_ = v_r_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_636_, v_b_637_);
lean_dec(v_as_x27_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object* v_m_639_, lean_object* v_l_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_l_640_, v_m_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(lean_object* v_m_642_, lean_object* v_l_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_642_, v_l_643_);
lean_dec(v_l_643_);
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
v___x_720_ = lean_unsigned_to_nat(16u);
v___x_721_ = lean_mk_array(v___x_720_, v___x_719_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36));
v___x_727_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_a_731_, lean_object* v_b_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_730_, v_a_731_, v_b_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object* v_as_734_, lean_object* v_as_x27_735_, lean_object* v_b_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_735_, v_b_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object* v_as_739_, lean_object* v_as_x27_740_, lean_object* v_b_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_as_739_, v_as_x27_740_, v_b_741_, v_a_742_);
lean_dec(v_as_x27_740_);
lean_dec(v_as_739_);
return v_res_743_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_744_, lean_object* v_a_745_, lean_object* v_x_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_745_, v_x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_748_, lean_object* v_a_749_, lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_748_, v_a_749_, v_x_750_);
lean_dec(v_x_750_);
lean_dec(v_a_749_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_753_, lean_object* v_data_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_data_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_756_, lean_object* v_i_757_, lean_object* v_source_758_, lean_object* v_target_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v_i_757_, v_source_758_, v_target_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(lean_object* v_op_790_, lean_object* v_f_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_792_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_873_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_873_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_873_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_873_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v_ring_809_; 
v_ring_809_ = lean_ctor_get_uint8(v_a_805_, sizeof(void*)*14 + 21);
lean_dec(v_a_805_);
if (v_ring_809_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_box(v_ring_809_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_853_);
v___x_855_ = v___x_807_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
if (lean_obj_tag(v_f_791_) == 4)
{
lean_object* v_declName_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
lean_del_object(v___x_807_);
v_declName_857_ = lean_ctor_get(v_f_791_, 0);
v___x_858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2));
v___x_859_ = lean_name_eq(v_declName_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5));
v___x_861_ = lean_name_eq(v_declName_857_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8));
v___x_863_ = lean_name_eq(v_declName_857_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11));
v___x_865_ = lean_name_eq(v_declName_857_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14));
v___x_867_ = lean_name_eq(v_declName_857_, v___x_866_);
if (v___x_867_ == 0)
{
goto v___jp_800_;
}
else
{
goto v___jp_810_;
}
}
else
{
goto v___jp_810_;
}
}
else
{
goto v___jp_810_;
}
}
else
{
goto v___jp_810_;
}
}
else
{
goto v___jp_810_;
}
}
else
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = 0;
v___x_869_ = lean_box(v___x_868_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_869_);
v___x_871_ = v___x_807_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
v___jp_810_:
{
lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_811_ = l_Lean_Expr_getAppNumArgs(v_op_790_);
v___x_812_ = lean_unsigned_to_nat(4u);
v___x_813_ = lean_nat_dec_eq(v___x_811_, v___x_812_);
lean_dec(v___x_811_);
if (v___x_813_ == 0)
{
goto v___jp_800_;
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_814_ = l_Lean_Expr_appFn_x21(v_op_790_);
v___x_815_ = l_Lean_Expr_appFn_x21(v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Lean_Expr_appArg_x21(v___x_815_);
lean_dec_ref(v___x_815_);
lean_inc_ref(v___x_816_);
v___x_817_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v___x_816_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_844_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_844_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_844_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_844_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
if (lean_obj_tag(v_a_818_) == 0)
{
lean_object* v___x_822_; 
lean_del_object(v___x_820_);
v___x_822_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v___x_816_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
if (lean_obj_tag(v_a_823_) == 0)
{
lean_del_object(v___x_825_);
goto v___jp_800_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec_ref_known(v_a_823_, 1);
v___x_827_ = lean_box(v_ring_809_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_822_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec_ref_known(v_a_818_, 1);
lean_dec_ref(v___x_816_);
v___x_840_ = lean_box(v_ring_809_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_840_);
v___x_842_ = v___x_820_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___x_816_);
v_a_845_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_817_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_817_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_804_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_804_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
v___jp_800_:
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = 0;
v___x_802_ = lean_box(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___boxed(lean_object* v_op_882_, lean_object* v_f_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_882_, v_f_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec_ref(v_f_883_);
lean_dec_ref(v_op_882_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* v_op_893_, lean_object* v_f_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_893_, v_f_894_, v_a_897_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* v_op_907_, lean_object* v_f_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_907_, v_f_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_f_908_);
lean_dec_ref(v_op_907_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_921_, lean_object* v_vals_922_, lean_object* v_i_923_, lean_object* v_k_924_){
_start:
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = lean_array_get_size(v_keys_921_);
v___x_926_ = lean_nat_dec_lt(v_i_923_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v_i_923_);
v___x_927_ = lean_box(0);
return v___x_927_;
}
else
{
lean_object* v_k_x27_928_; size_t v___x_929_; size_t v___x_930_; uint8_t v___x_931_; 
v_k_x27_928_ = lean_array_fget_borrowed(v_keys_921_, v_i_923_);
v___x_929_ = lean_ptr_addr(v_k_924_);
v___x_930_ = lean_ptr_addr(v_k_x27_928_);
v___x_931_ = lean_usize_dec_eq(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_add(v_i_923_, v___x_932_);
lean_dec(v_i_923_);
v_i_923_ = v___x_933_;
goto _start;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_array_fget_borrowed(v_vals_922_, v_i_923_);
lean_dec(v_i_923_);
lean_inc(v___x_935_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_937_, lean_object* v_vals_938_, lean_object* v_i_939_, lean_object* v_k_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_937_, v_vals_938_, v_i_939_, v_k_940_);
lean_dec_ref(v_k_940_);
lean_dec_ref(v_vals_938_);
lean_dec_ref(v_keys_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* v_x_942_, size_t v_x_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_object* v_es_945_; lean_object* v___x_946_; size_t v___x_947_; size_t v___x_948_; lean_object* v_j_949_; lean_object* v___x_950_; 
v_es_945_ = lean_ctor_get(v_x_942_, 0);
v___x_946_ = lean_box(2);
v___x_947_ = ((size_t)31ULL);
v___x_948_ = lean_usize_land(v_x_943_, v___x_947_);
v_j_949_ = lean_usize_to_nat(v___x_948_);
v___x_950_ = lean_array_get_borrowed(v___x_946_, v_es_945_, v_j_949_);
lean_dec(v_j_949_);
switch(lean_obj_tag(v___x_950_))
{
case 0:
{
lean_object* v_key_951_; lean_object* v_val_952_; size_t v___x_953_; size_t v___x_954_; uint8_t v___x_955_; 
v_key_951_ = lean_ctor_get(v___x_950_, 0);
v_val_952_ = lean_ctor_get(v___x_950_, 1);
v___x_953_ = lean_ptr_addr(v_x_944_);
v___x_954_ = lean_ptr_addr(v_key_951_);
v___x_955_ = lean_usize_dec_eq(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_box(0);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
lean_inc(v_val_952_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v_val_952_);
return v___x_957_;
}
}
case 1:
{
lean_object* v_node_958_; size_t v___x_959_; size_t v___x_960_; 
v_node_958_ = lean_ctor_get(v___x_950_, 0);
v___x_959_ = ((size_t)5ULL);
v___x_960_ = lean_usize_shift_right(v_x_943_, v___x_959_);
v_x_942_ = v_node_958_;
v_x_943_ = v___x_960_;
goto _start;
}
default: 
{
lean_object* v___x_962_; 
v___x_962_ = lean_box(0);
return v___x_962_;
}
}
}
else
{
lean_object* v_ks_963_; lean_object* v_vs_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_ks_963_ = lean_ctor_get(v_x_942_, 0);
v_vs_964_ = lean_ctor_get(v_x_942_, 1);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_963_, v_vs_964_, v___x_965_, v_x_944_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
size_t v_x_987__boxed_970_; lean_object* v_res_971_; 
v_x_987__boxed_970_ = lean_unbox_usize(v_x_968_);
lean_dec(v_x_968_);
v_res_971_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_967_, v_x_987__boxed_970_, v_x_969_);
lean_dec_ref(v_x_969_);
lean_dec_ref(v_x_967_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; uint64_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; 
v___x_974_ = lean_ptr_addr(v_x_973_);
v___x_975_ = ((size_t)3ULL);
v___x_976_ = lean_usize_shift_right(v___x_974_, v___x_975_);
v___x_977_ = lean_usize_to_uint64(v___x_976_);
v___x_978_ = lean_uint64_to_usize(v___x_977_);
v___x_979_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_972_, v___x_978_, v_x_973_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_980_, v_x_981_);
lean_dec_ref(v_x_981_);
lean_dec_ref(v_x_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* v_e_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1002_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_exprToOpIds_992_; lean_object* v___x_993_; 
v_exprToOpIds_992_ = lean_ctor_get(v_a_988_, 2);
lean_inc_ref(v_exprToOpIds_992_);
lean_dec(v_a_988_);
v___x_993_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_992_, v_e_983_);
lean_dec_ref(v_exprToOpIds_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_994_);
v___x_996_ = v___x_990_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v_val_998_; lean_object* v___x_1000_; 
v_val_998_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_993_, 1);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_val_998_);
v___x_1000_ = v___x_990_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_987_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_987_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1011_, v_a_1012_, v_a_1013_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_e_1011_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1016_, v_a_1017_, v_a_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* v_e_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_e_1029_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(v_00_u03b2_1046_, v_x_1047_, v_x_1048_);
lean_dec_ref(v_x_1048_);
lean_dec_ref(v_x_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, size_t v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
size_t v_x_1118__boxed_1059_; lean_object* v_res_1060_; 
v_x_1118__boxed_1059_ = lean_unbox_usize(v_x_1057_);
lean_dec(v_x_1057_);
v_res_1060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_1055_, v_x_1056_, v_x_1118__boxed_1059_, v_x_1058_);
lean_dec_ref(v_x_1058_);
lean_dec_ref(v_x_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1065_, v_k_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_1068_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_k_1073_);
lean_dec_ref(v_k_1073_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* v_opId_1075_, lean_object* v_a_1076_){
_start:
{
if (lean_obj_tag(v_a_1076_) == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_opId_1075_);
lean_ctor_set(v___x_1077_, 1, v_a_1076_);
return v___x_1077_;
}
else
{
lean_object* v_head_1078_; lean_object* v_tail_1079_; uint8_t v___x_1080_; 
v_head_1078_ = lean_ctor_get(v_a_1076_, 0);
v_tail_1079_ = lean_ctor_get(v_a_1076_, 1);
v___x_1080_ = lean_nat_dec_lt(v_opId_1075_, v_head_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1092_; 
lean_inc(v_tail_1079_);
lean_inc(v_head_1078_);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1093_ = lean_ctor_get(v_a_1076_, 1);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_a_1076_, 0);
lean_dec(v_unused_1094_);
v___x_1082_ = v_a_1076_;
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_a_1076_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_eq(v_opId_1075_, v_head_1078_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1075_, v_tail_1079_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_head_1078_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v___x_1090_; 
lean_dec(v_head_1078_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_opId_1075_);
v___x_1090_ = v___x_1082_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_opId_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_tail_1079_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_opId_1075_);
lean_ctor_set(v___x_1095_, 1, v_a_1076_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v_ks_1100_; lean_object* v_vs_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1127_; 
v_ks_1100_ = lean_ctor_get(v_x_1096_, 0);
v_vs_1101_ = lean_ctor_get(v_x_1096_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1103_ = v_x_1096_;
v_isShared_1104_ = v_isSharedCheck_1127_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_vs_1101_);
lean_inc(v_ks_1100_);
lean_dec(v_x_1096_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1127_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_array_get_size(v_ks_1100_);
v___x_1106_ = lean_nat_dec_lt(v_x_1097_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec(v_x_1097_);
v___x_1107_ = lean_array_push(v_ks_1100_, v_x_1098_);
v___x_1108_ = lean_array_push(v_vs_1101_, v_x_1099_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v___x_1108_);
lean_ctor_set(v___x_1103_, 0, v___x_1107_);
v___x_1110_ = v___x_1103_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v_k_x27_1112_; size_t v___x_1113_; size_t v___x_1114_; uint8_t v___x_1115_; 
v_k_x27_1112_ = lean_array_fget_borrowed(v_ks_1100_, v_x_1097_);
v___x_1113_ = lean_ptr_addr(v_x_1098_);
v___x_1114_ = lean_ptr_addr(v_k_x27_1112_);
v___x_1115_ = lean_usize_dec_eq(v___x_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1117_; 
if (v_isShared_1104_ == 0)
{
v___x_1117_ = v___x_1103_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_ks_1100_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_vs_1101_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_x_1097_, v___x_1118_);
lean_dec(v_x_1097_);
v_x_1096_ = v___x_1117_;
v_x_1097_ = v___x_1119_;
goto _start;
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1122_ = lean_array_fset(v_ks_1100_, v_x_1097_, v_x_1098_);
v___x_1123_ = lean_array_fset(v_vs_1101_, v_x_1097_, v_x_1099_);
lean_dec(v_x_1097_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v___x_1123_);
lean_ctor_set(v___x_1103_, 0, v___x_1122_);
v___x_1125_ = v___x_1103_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1128_, lean_object* v_k_1129_, lean_object* v_v_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1128_, v___x_1131_, v_k_1129_, v_v_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* v_x_1134_, size_t v_x_1135_, size_t v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_object* v_es_1139_; size_t v___x_1140_; size_t v___x_1141_; lean_object* v_j_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_es_1139_ = lean_ctor_get(v_x_1134_, 0);
v___x_1140_ = ((size_t)31ULL);
v___x_1141_ = lean_usize_land(v_x_1135_, v___x_1140_);
v_j_1142_ = lean_usize_to_nat(v___x_1141_);
v___x_1143_ = lean_array_get_size(v_es_1139_);
v___x_1144_ = lean_nat_dec_lt(v_j_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec(v_j_1142_);
lean_dec(v_x_1138_);
lean_dec_ref(v_x_1137_);
return v_x_1134_;
}
else
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1185_; 
lean_inc_ref(v_es_1139_);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_x_1134_, 0);
lean_dec(v_unused_1186_);
v___x_1146_ = v_x_1134_;
v_isShared_1147_ = v_isSharedCheck_1185_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v_x_1134_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1185_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_v_1148_; lean_object* v___x_1149_; lean_object* v_xs_x27_1150_; lean_object* v___y_1152_; 
v_v_1148_ = lean_array_fget(v_es_1139_, v_j_1142_);
v___x_1149_ = lean_box(0);
v_xs_x27_1150_ = lean_array_fset(v_es_1139_, v_j_1142_, v___x_1149_);
switch(lean_obj_tag(v_v_1148_))
{
case 0:
{
lean_object* v_key_1157_; lean_object* v_val_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
v_key_1157_ = lean_ctor_get(v_v_1148_, 0);
v_val_1158_ = lean_ctor_get(v_v_1148_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_v_1148_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v_v_1148_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_val_1158_);
lean_inc(v_key_1157_);
lean_dec(v_v_1148_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
size_t v___x_1162_; size_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_ptr_addr(v_x_1137_);
v___x_1163_ = lean_ptr_addr(v_key_1157_);
v___x_1164_ = lean_usize_dec_eq(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_1160_);
v___x_1165_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1157_, v_val_1158_, v_x_1137_, v_x_1138_);
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___y_1152_ = v___x_1166_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v_val_1158_);
lean_dec(v_key_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v_x_1138_);
lean_ctor_set(v___x_1160_, 0, v_x_1137_);
v___x_1168_ = v___x_1160_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_x_1137_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_x_1138_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v___y_1152_ = v___x_1168_;
goto v___jp_1151_;
}
}
}
}
case 1:
{
lean_object* v_node_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1183_; 
v_node_1171_ = lean_ctor_get(v_v_1148_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_v_1148_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1173_ = v_v_1148_;
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_node_1171_);
lean_dec(v_v_1148_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1175_ = ((size_t)5ULL);
v___x_1176_ = lean_usize_shift_right(v_x_1135_, v___x_1175_);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_x_1136_, v___x_1177_);
v___x_1179_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_1171_, v___x_1176_, v___x_1178_, v_x_1137_, v_x_1138_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1179_);
v___x_1181_ = v___x_1173_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v___y_1152_ = v___x_1181_;
goto v___jp_1151_;
}
}
}
default: 
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_x_1137_);
lean_ctor_set(v___x_1184_, 1, v_x_1138_);
v___y_1152_ = v___x_1184_;
goto v___jp_1151_;
}
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_array_fset(v_xs_x27_1150_, v_j_1142_, v___y_1152_);
lean_dec(v_j_1142_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1153_);
v___x_1155_ = v___x_1146_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
else
{
lean_object* v_ks_1187_; lean_object* v_vs_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1206_; 
v_ks_1187_ = lean_ctor_get(v_x_1134_, 0);
v_vs_1188_ = lean_ctor_get(v_x_1134_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1190_ = v_x_1134_;
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_vs_1188_);
lean_inc(v_ks_1187_);
lean_dec(v_x_1134_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1206_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_ks_1187_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_vs_1188_);
v___x_1193_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v_newNode_1194_; size_t v___x_1195_; uint8_t v___x_1196_; 
v_newNode_1194_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_1193_, v_x_1137_, v_x_1138_);
v___x_1195_ = ((size_t)7ULL);
v___x_1196_ = lean_usize_dec_le(v___x_1195_, v_x_1136_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1194_);
v___x_1198_ = lean_unsigned_to_nat(4u);
v___x_1199_ = lean_nat_dec_lt(v___x_1197_, v___x_1198_);
lean_dec(v___x_1197_);
if (v___x_1199_ == 0)
{
lean_object* v_ks_1200_; lean_object* v_vs_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_ks_1200_ = lean_ctor_get(v_newNode_1194_, 0);
lean_inc_ref(v_ks_1200_);
v_vs_1201_ = lean_ctor_get(v_newNode_1194_, 1);
lean_inc_ref(v_vs_1201_);
lean_dec_ref(v_newNode_1194_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
v___x_1204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_1136_, v_ks_1200_, v_vs_1201_, v___x_1202_, v___x_1203_);
lean_dec_ref(v_vs_1201_);
lean_dec_ref(v_ks_1200_);
return v___x_1204_;
}
else
{
return v_newNode_1194_;
}
}
else
{
return v_newNode_1194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1207_, lean_object* v_keys_1208_, lean_object* v_vals_1209_, lean_object* v_i_1210_, lean_object* v_entries_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_keys_1208_);
v___x_1213_ = lean_nat_dec_lt(v_i_1210_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec(v_i_1210_);
return v_entries_1211_;
}
else
{
lean_object* v_k_1214_; lean_object* v_v_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; uint64_t v___x_1219_; size_t v_h_1220_; size_t v___x_1221_; lean_object* v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v_h_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_k_1214_ = lean_array_fget_borrowed(v_keys_1208_, v_i_1210_);
v_v_1215_ = lean_array_fget_borrowed(v_vals_1209_, v_i_1210_);
v___x_1216_ = lean_ptr_addr(v_k_1214_);
v___x_1217_ = ((size_t)3ULL);
v___x_1218_ = lean_usize_shift_right(v___x_1216_, v___x_1217_);
v___x_1219_ = lean_usize_to_uint64(v___x_1218_);
v_h_1220_ = lean_uint64_to_usize(v___x_1219_);
v___x_1221_ = ((size_t)5ULL);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_sub(v_depth_1207_, v___x_1223_);
v___x_1225_ = lean_usize_mul(v___x_1221_, v___x_1224_);
v_h_1226_ = lean_usize_shift_right(v_h_1220_, v___x_1225_);
v___x_1227_ = lean_nat_add(v_i_1210_, v___x_1222_);
lean_dec(v_i_1210_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
v___x_1228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_1211_, v_h_1226_, v_depth_1207_, v_k_1214_, v_v_1215_);
v_i_1210_ = v___x_1227_;
v_entries_1211_ = v___x_1228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1230_, lean_object* v_keys_1231_, lean_object* v_vals_1232_, lean_object* v_i_1233_, lean_object* v_entries_1234_){
_start:
{
size_t v_depth_boxed_1235_; lean_object* v_res_1236_; 
v_depth_boxed_1235_ = lean_unbox_usize(v_depth_1230_);
lean_dec(v_depth_1230_);
v_res_1236_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1235_, v_keys_1231_, v_vals_1232_, v_i_1233_, v_entries_1234_);
lean_dec_ref(v_vals_1232_);
lean_dec_ref(v_keys_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
size_t v_x_443__boxed_1242_; size_t v_x_444__boxed_1243_; lean_object* v_res_1244_; 
v_x_443__boxed_1242_ = lean_unbox_usize(v_x_1238_);
lean_dec(v_x_1238_);
v_x_444__boxed_1243_ = lean_unbox_usize(v_x_1239_);
lean_dec(v_x_1239_);
v_res_1244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1237_, v_x_443__boxed_1242_, v_x_444__boxed_1243_, v_x_1240_, v_x_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; uint64_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1248_ = lean_ptr_addr(v_x_1246_);
v___x_1249_ = ((size_t)3ULL);
v___x_1250_ = lean_usize_shift_right(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_usize_to_uint64(v___x_1250_);
v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1245_, v___x_1252_, v___x_1253_, v_x_1246_, v_x_1247_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* v_m_1255_, lean_object* v_e_1256_, lean_object* v_opId_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_m_1255_, v_e_1256_);
if (lean_obj_tag(v___x_1258_) == 1)
{
lean_object* v_val_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_val_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1257_, v_val_1259_);
v___x_1261_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1255_, v_e_1256_, v___x_1260_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v___x_1258_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_opId_1257_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1255_, v_e_1256_, v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_1266_, v_x_1267_, v_x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* v_00_u03b2_1270_, lean_object* v_x_1271_, size_t v_x_1272_, size_t v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1271_, v_x_1272_, v_x_1273_, v_x_1274_, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
size_t v_x_644__boxed_1283_; size_t v_x_645__boxed_1284_; lean_object* v_res_1285_; 
v_x_644__boxed_1283_ = lean_unbox_usize(v_x_1279_);
lean_dec(v_x_1279_);
v_x_645__boxed_1284_ = lean_unbox_usize(v_x_1280_);
lean_dec(v_x_1280_);
v_res_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_1277_, v_x_1278_, v_x_644__boxed_1283_, v_x_645__boxed_1284_, v_x_1281_, v_x_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1286_, lean_object* v_n_1287_, lean_object* v_k_1288_, lean_object* v_v_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_1287_, v_k_1288_, v_v_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1291_, size_t v_depth_1292_, lean_object* v_keys_1293_, lean_object* v_vals_1294_, lean_object* v_heq_1295_, lean_object* v_i_1296_, lean_object* v_entries_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1292_, v_keys_1293_, v_vals_1294_, v_i_1296_, v_entries_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1299_, lean_object* v_depth_1300_, lean_object* v_keys_1301_, lean_object* v_vals_1302_, lean_object* v_heq_1303_, lean_object* v_i_1304_, lean_object* v_entries_1305_){
_start:
{
size_t v_depth_boxed_1306_; lean_object* v_res_1307_; 
v_depth_boxed_1306_ = lean_unbox_usize(v_depth_1300_);
lean_dec(v_depth_1300_);
v_res_1307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_1299_, v_depth_boxed_1306_, v_keys_1301_, v_vals_1302_, v_heq_1303_, v_i_1304_, v_entries_1305_);
lean_dec_ref(v_vals_1302_);
lean_dec_ref(v_keys_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1309_, v_x_1310_, v_x_1311_, v_x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v_s_1316_){
_start:
{
lean_object* v_structs_1317_; lean_object* v_opIdOf_1318_; lean_object* v_exprToOpIds_1319_; lean_object* v_steps_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_structs_1317_ = lean_ctor_get(v_s_1316_, 0);
v_opIdOf_1318_ = lean_ctor_get(v_s_1316_, 1);
v_exprToOpIds_1319_ = lean_ctor_get(v_s_1316_, 2);
v_steps_1320_ = lean_ctor_get(v_s_1316_, 3);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_s_1316_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v_s_1316_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_steps_1320_);
lean_inc(v_exprToOpIds_1319_);
lean_inc(v_opIdOf_1318_);
lean_inc(v_structs_1317_);
lean_dec(v_s_1316_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_inc(v_a_1315_);
v___x_1324_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(v_exprToOpIds_1319_, v_e_1314_, v_a_1315_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 2, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_structs_1317_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_opIdOf_1318_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_steps_1320_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v_s_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_1329_, v_a_1330_, v_s_1331_);
lean_dec(v_a_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* v_e_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___f_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_inc(v_a_1334_);
v___f_1337_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1337_, 0, v_e_1333_);
lean_closure_set(v___f_1337_, 1, v_a_1334_);
v___x_1338_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1339_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1338_, v___f_1337_, v_a_1335_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec(v_a_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* v_e_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1345_, v_a_1346_, v_a_1347_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* v_e_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec(v_a_1360_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* v_e_1373_, lean_object* v_size_1374_, lean_object* v_s_1375_){
_start:
{
lean_object* v_id_1376_; lean_object* v_type_1377_; lean_object* v_u_1378_; lean_object* v_op_1379_; lean_object* v_neutral_x3f_1380_; lean_object* v_assocInst_1381_; lean_object* v_idempotentInst_x3f_1382_; lean_object* v_commInst_x3f_1383_; lean_object* v_neutralInst_x3f_1384_; lean_object* v_nextId_1385_; lean_object* v_vars_1386_; lean_object* v_varMap_1387_; lean_object* v_denote_1388_; lean_object* v_denoteEntries_1389_; lean_object* v_queue_1390_; lean_object* v_basis_1391_; lean_object* v_diseqs_1392_; uint8_t v_recheck_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v_id_1376_ = lean_ctor_get(v_s_1375_, 0);
v_type_1377_ = lean_ctor_get(v_s_1375_, 1);
v_u_1378_ = lean_ctor_get(v_s_1375_, 2);
v_op_1379_ = lean_ctor_get(v_s_1375_, 3);
v_neutral_x3f_1380_ = lean_ctor_get(v_s_1375_, 4);
v_assocInst_1381_ = lean_ctor_get(v_s_1375_, 5);
v_idempotentInst_x3f_1382_ = lean_ctor_get(v_s_1375_, 6);
v_commInst_x3f_1383_ = lean_ctor_get(v_s_1375_, 7);
v_neutralInst_x3f_1384_ = lean_ctor_get(v_s_1375_, 8);
v_nextId_1385_ = lean_ctor_get(v_s_1375_, 9);
v_vars_1386_ = lean_ctor_get(v_s_1375_, 10);
v_varMap_1387_ = lean_ctor_get(v_s_1375_, 11);
v_denote_1388_ = lean_ctor_get(v_s_1375_, 12);
v_denoteEntries_1389_ = lean_ctor_get(v_s_1375_, 13);
v_queue_1390_ = lean_ctor_get(v_s_1375_, 14);
v_basis_1391_ = lean_ctor_get(v_s_1375_, 15);
v_diseqs_1392_ = lean_ctor_get(v_s_1375_, 16);
v_recheck_1393_ = lean_ctor_get_uint8(v_s_1375_, sizeof(void*)*17);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_s_1375_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1395_ = v_s_1375_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_diseqs_1392_);
lean_inc(v_basis_1391_);
lean_inc(v_queue_1390_);
lean_inc(v_denoteEntries_1389_);
lean_inc(v_denote_1388_);
lean_inc(v_varMap_1387_);
lean_inc(v_vars_1386_);
lean_inc(v_nextId_1385_);
lean_inc(v_neutralInst_x3f_1384_);
lean_inc(v_commInst_x3f_1383_);
lean_inc(v_idempotentInst_x3f_1382_);
lean_inc(v_assocInst_1381_);
lean_inc(v_neutral_x3f_1380_);
lean_inc(v_op_1379_);
lean_inc(v_u_1378_);
lean_inc(v_type_1377_);
lean_inc(v_id_1376_);
lean_dec(v_s_1375_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_inc_ref(v_e_1373_);
v___x_1397_ = l_Lean_PersistentArray_push___redArg(v_vars_1386_, v_e_1373_);
v___x_1398_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_1387_, v_e_1373_, v_size_1374_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 11, v___x_1398_);
lean_ctor_set(v___x_1395_, 10, v___x_1397_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_id_1376_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_type_1377_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_u_1378_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_op_1379_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_neutral_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1401_, 5, v_assocInst_1381_);
lean_ctor_set(v_reuseFailAlloc_1401_, 6, v_idempotentInst_x3f_1382_);
lean_ctor_set(v_reuseFailAlloc_1401_, 7, v_commInst_x3f_1383_);
lean_ctor_set(v_reuseFailAlloc_1401_, 8, v_neutralInst_x3f_1384_);
lean_ctor_set(v_reuseFailAlloc_1401_, 9, v_nextId_1385_);
lean_ctor_set(v_reuseFailAlloc_1401_, 10, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1401_, 11, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1401_, 12, v_denote_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 13, v_denoteEntries_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 14, v_queue_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 15, v_basis_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 16, v_diseqs_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*17, v_recheck_1393_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1466_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1466_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1466_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_vars_1421_; lean_object* v_varMap_1422_; lean_object* v___x_1423_; 
v_vars_1421_ = lean_ctor_get(v_a_1417_, 10);
lean_inc_ref(v_vars_1421_);
v_varMap_1422_ = lean_ctor_get(v_a_1417_, 11);
lean_inc_ref(v_varMap_1422_);
lean_dec(v_a_1417_);
v___x_1423_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_1422_, v_e_1403_);
lean_dec_ref(v_varMap_1422_);
if (lean_obj_tag(v___x_1423_) == 1)
{
lean_object* v_val_1424_; lean_object* v___x_1426_; 
lean_dec_ref(v_vars_1421_);
lean_dec_ref(v_e_1403_);
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1423_, 1);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v_val_1424_);
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_val_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v_size_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; 
lean_dec(v___x_1423_);
lean_del_object(v___x_1419_);
v_size_1428_ = lean_ctor_get(v_vars_1421_, 2);
lean_inc_n(v_size_1428_, 2);
lean_dec_ref(v_vars_1421_);
lean_inc_ref(v_e_1403_);
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(v___f_1429_, 0, v_e_1403_);
lean_closure_set(v___f_1429_, 1, v_size_1428_);
v___x_1430_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_1429_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1430_, 1);
lean_inc_ref(v_e_1403_);
v___x_1431_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref_known(v___x_1431_, 1);
v___x_1432_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1433_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1432_, v_e_1403_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1441_);
v___x_1435_ = v___x_1433_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v___x_1433_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v_size_1428_);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_size_1428_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_size_1428_);
v_a_1442_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1433_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1433_);
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
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_size_1428_);
lean_dec_ref(v_e_1403_);
v_a_1450_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1431_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1431_);
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
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_size_1428_);
lean_dec_ref(v_e_1403_);
v_a_1458_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1430_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1430_);
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
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_e_1403_);
v_a_1467_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1416_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1416_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec(v_a_1476_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* v_e_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_mctx_1493_; lean_object* v___x_1494_; lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1497_; lean_object* v_cache_1498_; lean_object* v_zetaDeltaFVarIds_1499_; lean_object* v_postponed_1500_; lean_object* v_diag_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1510_; 
v___x_1492_ = lean_st_ref_get(v___y_1490_);
v_mctx_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_mctx_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = lean_instantiate_expr_mvars(v_mctx_1493_, v_e_1489_);
v_fst_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_fst_1495_);
v_snd_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_snd_1496_);
lean_dec_ref(v___x_1494_);
v___x_1497_ = lean_st_ref_take(v___y_1490_);
v_cache_1498_ = lean_ctor_get(v___x_1497_, 1);
v_zetaDeltaFVarIds_1499_ = lean_ctor_get(v___x_1497_, 2);
v_postponed_1500_ = lean_ctor_get(v___x_1497_, 3);
v_diag_1501_ = lean_ctor_get(v___x_1497_, 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1497_, 0);
lean_dec(v_unused_1511_);
v___x_1503_ = v___x_1497_;
v_isShared_1504_ = v_isSharedCheck_1510_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_diag_1501_);
lean_inc(v_postponed_1500_);
lean_inc(v_zetaDeltaFVarIds_1499_);
lean_inc(v_cache_1498_);
lean_dec(v___x_1497_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1510_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v_fst_1495_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_fst_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_cache_1498_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_zetaDeltaFVarIds_1499_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_postponed_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_diag_1501_);
v___x_1506_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_st_ref_put(v___y_1490_, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_snd_1496_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1512_, v___y_1513_);
lean_dec(v___y_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* v_e_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1516_, v___y_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* v_e_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec(v___y_1530_);
return v_res_1541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_unsigned_to_nat(32u);
v___x_1543_ = lean_mk_empty_array_with_capacity(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1(void){
_start:
{
size_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1545_ = ((size_t)5ULL);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_unsigned_to_nat(32u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
v___x_1550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1548_);
lean_ctor_set(v___x_1550_, 2, v___x_1546_);
lean_ctor_set(v___x_1550_, 3, v___x_1546_);
lean_ctor_set_usize(v___x_1550_, 4, v___x_1545_);
return v___x_1550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1551_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* v___x_1554_, lean_object* v_binderType_1555_, lean_object* v_a_1556_, lean_object* v_op_1557_, lean_object* v_snd_1558_, lean_object* v_val_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_fst_1562_, uint8_t v_a_1563_, lean_object* v_s_1564_){
_start:
{
lean_object* v_structs_1565_; lean_object* v_opIdOf_1566_; lean_object* v_exprToOpIds_1567_; lean_object* v_steps_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1582_; 
v_structs_1565_ = lean_ctor_get(v_s_1564_, 0);
v_opIdOf_1566_ = lean_ctor_get(v_s_1564_, 1);
v_exprToOpIds_1567_ = lean_ctor_get(v_s_1564_, 2);
v_steps_1568_ = lean_ctor_get(v_s_1564_, 3);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_s_1564_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1570_ = v_s_1564_;
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_steps_1568_);
lean_inc(v_exprToOpIds_1567_);
lean_inc(v_opIdOf_1566_);
lean_inc(v_structs_1565_);
lean_dec(v_s_1564_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1582_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
v___x_1574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
v___x_1575_ = lean_box(1);
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_1577_, 0, v___x_1554_);
lean_ctor_set(v___x_1577_, 1, v_binderType_1555_);
lean_ctor_set(v___x_1577_, 2, v_a_1556_);
lean_ctor_set(v___x_1577_, 3, v_op_1557_);
lean_ctor_set(v___x_1577_, 4, v_snd_1558_);
lean_ctor_set(v___x_1577_, 5, v_val_1559_);
lean_ctor_set(v___x_1577_, 6, v_a_1560_);
lean_ctor_set(v___x_1577_, 7, v_a_1561_);
lean_ctor_set(v___x_1577_, 8, v_fst_1562_);
lean_ctor_set(v___x_1577_, 9, v___x_1572_);
lean_ctor_set(v___x_1577_, 10, v___x_1573_);
lean_ctor_set(v___x_1577_, 11, v___x_1574_);
lean_ctor_set(v___x_1577_, 12, v___x_1574_);
lean_ctor_set(v___x_1577_, 13, v___x_1573_);
lean_ctor_set(v___x_1577_, 14, v___x_1575_);
lean_ctor_set(v___x_1577_, 15, v___x_1576_);
lean_ctor_set(v___x_1577_, 16, v___x_1573_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*17, v_a_1563_);
v___x_1578_ = lean_array_push(v_structs_1565_, v___x_1577_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1578_);
v___x_1580_ = v___x_1570_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_opIdOf_1566_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_exprToOpIds_1567_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_steps_1568_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* v___x_1583_, lean_object* v_binderType_1584_, lean_object* v_a_1585_, lean_object* v_op_1586_, lean_object* v_snd_1587_, lean_object* v_val_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_fst_1591_, lean_object* v_a_1592_, lean_object* v_s_1593_){
_start:
{
uint8_t v_a_121647__boxed_1594_; lean_object* v_res_1595_; 
v_a_121647__boxed_1594_ = lean_unbox(v_a_1592_);
v_res_1595_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1583_, v_binderType_1584_, v_a_1585_, v_op_1586_, v_snd_1587_, v_val_1588_, v_a_1589_, v_a_1590_, v_fst_1591_, v_a_121647__boxed_1594_, v_s_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* v_m_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_buckets_1598_; lean_object* v___x_1599_; uint64_t v___y_1601_; 
v_buckets_1598_ = lean_ctor_get(v_m_1596_, 1);
v___x_1599_ = lean_array_get_size(v_buckets_1598_);
if (lean_obj_tag(v_a_1597_) == 0)
{
uint64_t v___x_1615_; 
v___x_1615_ = 1723ULL;
v___y_1601_ = v___x_1615_;
goto v___jp_1600_;
}
else
{
uint64_t v_hash_1616_; 
v_hash_1616_ = lean_ctor_get_uint64(v_a_1597_, sizeof(void*)*2);
v___y_1601_ = v_hash_1616_;
goto v___jp_1600_;
}
v___jp_1600_:
{
uint64_t v___x_1602_; uint64_t v___x_1603_; uint64_t v_fold_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; uint64_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1602_ = 32ULL;
v___x_1603_ = lean_uint64_shift_right(v___y_1601_, v___x_1602_);
v_fold_1604_ = lean_uint64_xor(v___y_1601_, v___x_1603_);
v___x_1605_ = 16ULL;
v___x_1606_ = lean_uint64_shift_right(v_fold_1604_, v___x_1605_);
v___x_1607_ = lean_uint64_xor(v_fold_1604_, v___x_1606_);
v___x_1608_ = lean_uint64_to_usize(v___x_1607_);
v___x_1609_ = lean_usize_of_nat(v___x_1599_);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_sub(v___x_1609_, v___x_1610_);
v___x_1612_ = lean_usize_land(v___x_1608_, v___x_1611_);
v___x_1613_ = lean_array_uget_borrowed(v_buckets_1598_, v___x_1612_);
v___x_1614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_1597_, v___x_1613_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* v_m_1617_, lean_object* v_a_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_m_1617_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1621_; double v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_float_of_nat(v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* v_cls_1626_, lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_ref_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1680_; 
v_ref_1633_ = lean_ctor_get(v___y_1630_, 2);
v___x_1634_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1680_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1680_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v_traceState_1640_; lean_object* v_env_1641_; lean_object* v_nextMacroScope_1642_; lean_object* v_ngen_1643_; lean_object* v_auxDeclNGen_1644_; lean_object* v_cache_1645_; lean_object* v_recordedDeps_1646_; lean_object* v_messages_1647_; lean_object* v_infoState_1648_; lean_object* v_snapshotTasks_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1679_; 
v___x_1639_ = lean_st_ref_take(v___y_1631_);
v_traceState_1640_ = lean_ctor_get(v___x_1639_, 4);
v_env_1641_ = lean_ctor_get(v___x_1639_, 0);
v_nextMacroScope_1642_ = lean_ctor_get(v___x_1639_, 1);
v_ngen_1643_ = lean_ctor_get(v___x_1639_, 2);
v_auxDeclNGen_1644_ = lean_ctor_get(v___x_1639_, 3);
v_cache_1645_ = lean_ctor_get(v___x_1639_, 5);
v_recordedDeps_1646_ = lean_ctor_get(v___x_1639_, 6);
v_messages_1647_ = lean_ctor_get(v___x_1639_, 7);
v_infoState_1648_ = lean_ctor_get(v___x_1639_, 8);
v_snapshotTasks_1649_ = lean_ctor_get(v___x_1639_, 9);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1651_ = v___x_1639_;
v_isShared_1652_ = v_isSharedCheck_1679_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snapshotTasks_1649_);
lean_inc(v_infoState_1648_);
lean_inc(v_messages_1647_);
lean_inc(v_recordedDeps_1646_);
lean_inc(v_cache_1645_);
lean_inc(v_traceState_1640_);
lean_inc(v_auxDeclNGen_1644_);
lean_inc(v_ngen_1643_);
lean_inc(v_nextMacroScope_1642_);
lean_inc(v_env_1641_);
lean_dec(v___x_1639_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1679_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint64_t v_tid_1653_; lean_object* v_traces_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1678_; 
v_tid_1653_ = lean_ctor_get_uint64(v_traceState_1640_, sizeof(void*)*1);
v_traces_1654_ = lean_ctor_get(v_traceState_1640_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_traceState_1640_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1656_ = v_traceState_1640_;
v_isShared_1657_ = v_isSharedCheck_1678_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_traces_1654_);
lean_dec(v_traceState_1640_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1678_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; double v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
v___x_1661_ = 0;
v___x_1662_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
v___x_1663_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1663_, 0, v_cls_1626_);
lean_ctor_set(v___x_1663_, 1, v___x_1659_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
lean_ctor_set_float(v___x_1663_, sizeof(void*)*3, v___x_1660_);
lean_ctor_set_float(v___x_1663_, sizeof(void*)*3 + 8, v___x_1660_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*3 + 16, v___x_1661_);
v___x_1664_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2));
v___x_1665_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v_a_1635_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
lean_inc(v_ref_1633_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_ref_1633_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Lean_PersistentArray_push___redArg(v_traces_1654_, v___x_1666_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1667_);
v___x_1669_ = v___x_1656_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1667_);
lean_ctor_set_uint64(v_reuseFailAlloc_1677_, sizeof(void*)*1, v_tid_1653_);
v___x_1669_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v___x_1669_);
v___x_1671_ = v___x_1651_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_env_1641_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_nextMacroScope_1642_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_ngen_1643_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_auxDeclNGen_1644_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1676_, 5, v_cache_1645_);
lean_ctor_set(v_reuseFailAlloc_1676_, 6, v_recordedDeps_1646_);
lean_ctor_set(v_reuseFailAlloc_1676_, 7, v_messages_1647_);
lean_ctor_set(v_reuseFailAlloc_1676_, 8, v_infoState_1648_);
lean_ctor_set(v_reuseFailAlloc_1676_, 9, v_snapshotTasks_1649_);
v___x_1671_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = lean_st_ref_put(v___y_1631_, v___x_1671_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1658_);
v___x_1674_ = v___x_1637_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1658_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* v_cls_1681_, lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1681_, v_msg_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
v___x_1696_ = l_Lean_MessageData_ofFormat(v___x_1695_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15));
v___x_1716_ = l_Lean_Name_append(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* v_op_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___y_1750_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v_f_1906_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; 
v_f_1906_ = l_Lean_Expr_getAppFn(v_op_1737_);
if (lean_obj_tag(v_f_1906_) == 4)
{
lean_object* v_declName_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_declName_2169_ = lean_ctor_get(v_f_1906_, 0);
lean_inc(v_declName_2169_);
v___x_2170_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_2170_, v_declName_2169_);
lean_dec(v_declName_2169_);
if (v___x_2171_ == 0)
{
v___y_1908_ = v_a_1738_;
v___y_1909_ = v_a_1739_;
v___y_1910_ = v_a_1740_;
v___y_1911_ = v_a_1741_;
v___y_1912_ = v_a_1742_;
v___y_1913_ = v_a_1743_;
v___y_1914_ = v_a_1744_;
v___y_1915_ = v_a_1745_;
v___y_1916_ = v_a_1746_;
v___y_1917_ = v_a_1747_;
goto v___jp_1907_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_dec_ref_known(v_f_1906_, 2);
lean_dec_ref(v_op_1737_);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
else
{
v___y_1908_ = v_a_1738_;
v___y_1909_ = v_a_1739_;
v___y_1910_ = v_a_1740_;
v___y_1911_ = v_a_1741_;
v___y_1912_ = v_a_1742_;
v___y_1913_ = v_a_1743_;
v___y_1914_ = v_a_1744_;
v___y_1915_ = v_a_1745_;
v___y_1916_ = v_a_1746_;
v___y_1917_ = v_a_1747_;
goto v___jp_1907_;
}
v___jp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___y_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1755_) == 1)
{
lean_object* v_val_1766_; lean_object* v___x_1767_; 
v_val_1766_ = lean_ctor_get(v___y_1755_, 0);
lean_inc(v_val_1766_);
lean_dec_ref_known(v___y_1755_, 1);
v___x_1767_ = l_Lean_Meta_Grind_AC_mkVar(v_val_1766_, v___y_1754_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_dec_ref_known(v___x_1767_, 1);
v___y_1750_ = v___y_1754_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v___y_1754_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_dec(v___y_1755_);
v___y_1750_ = v___y_1754_;
goto v___jp_1749_;
}
}
v___jp_1776_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1790_);
lean_ctor_set(v___x_1792_, 1, v___y_1791_);
lean_inc(v___y_1785_);
v___x_1793_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_1785_, v___x_1792_, v___y_1789_, v___y_1781_, v___y_1778_, v___y_1786_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_dec_ref_known(v___x_1793_, 1);
v___y_1754_ = v___y_1779_;
v___y_1755_ = v___y_1784_;
v___y_1756_ = v___y_1777_;
v___y_1757_ = v___y_1788_;
v___y_1758_ = v___y_1783_;
v___y_1759_ = v___y_1782_;
v___y_1760_ = v___y_1787_;
v___y_1761_ = v___y_1780_;
v___y_1762_ = v___y_1789_;
v___y_1763_ = v___y_1781_;
v___y_1764_ = v___y_1778_;
v___y_1765_ = v___y_1786_;
goto v___jp_1753_;
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v___y_1784_);
lean_dec(v___y_1779_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
v___jp_1802_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc_ref(v___y_1817_);
v___x_1818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___y_1817_);
v___x_1819_ = l_Lean_MessageData_ofFormat(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___y_1805_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
if (lean_obj_tag(v___y_1811_) == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___y_1804_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1807_;
v___y_1781_ = v___y_1808_;
v___y_1782_ = v___y_1809_;
v___y_1783_ = v___y_1810_;
v___y_1784_ = v___y_1811_;
v___y_1785_ = v___y_1812_;
v___y_1786_ = v___y_1813_;
v___y_1787_ = v___y_1814_;
v___y_1788_ = v___y_1815_;
v___y_1789_ = v___y_1816_;
v___y_1790_ = v___x_1822_;
v___y_1791_ = v___x_1823_;
goto v___jp_1776_;
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1825_; 
v_val_1824_ = lean_ctor_get(v___y_1811_, 0);
lean_inc(v_val_1824_);
v___x_1825_ = l_Lean_MessageData_ofExpr(v_val_1824_);
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___y_1804_;
v___y_1779_ = v___y_1806_;
v___y_1780_ = v___y_1807_;
v___y_1781_ = v___y_1808_;
v___y_1782_ = v___y_1809_;
v___y_1783_ = v___y_1810_;
v___y_1784_ = v___y_1811_;
v___y_1785_ = v___y_1812_;
v___y_1786_ = v___y_1813_;
v___y_1787_ = v___y_1814_;
v___y_1788_ = v___y_1815_;
v___y_1789_ = v___y_1816_;
v___y_1790_ = v___x_1822_;
v___y_1791_ = v___x_1825_;
goto v___jp_1776_;
}
}
v___jp_1826_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_inc_ref(v___y_1842_);
v___x_1843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1842_);
v___x_1844_ = l_Lean_MessageData_ofFormat(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___y_1832_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
if (lean_obj_tag(v___y_1840_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1803_ = v___y_1827_;
v___y_1804_ = v___y_1828_;
v___y_1805_ = v___x_1847_;
v___y_1806_ = v___y_1829_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___y_1833_;
v___y_1810_ = v___y_1834_;
v___y_1811_ = v___y_1835_;
v___y_1812_ = v___y_1836_;
v___y_1813_ = v___y_1837_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___x_1848_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v___y_1840_, 1);
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1803_ = v___y_1827_;
v___y_1804_ = v___y_1828_;
v___y_1805_ = v___x_1847_;
v___y_1806_ = v___y_1829_;
v___y_1807_ = v___y_1830_;
v___y_1808_ = v___y_1831_;
v___y_1809_ = v___y_1833_;
v___y_1810_ = v___y_1834_;
v___y_1811_ = v___y_1835_;
v___y_1812_ = v___y_1836_;
v___y_1813_ = v___y_1837_;
v___y_1814_ = v___y_1838_;
v___y_1815_ = v___y_1839_;
v___y_1816_ = v___y_1841_;
v___y_1817_ = v___x_1849_;
goto v___jp_1802_;
}
}
v___jp_1850_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_1860_, v___y_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v_structs_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v_structs_1872_ = lean_ctor_get(v_a_1871_, 0);
lean_inc_ref(v_structs_1872_);
lean_dec(v_a_1871_);
v___x_1873_ = lean_array_get_size(v_structs_1872_);
lean_dec_ref(v_structs_1872_);
v___x_1874_ = lean_box(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc(v_snd_1859_);
lean_inc_ref(v_op_1737_);
v___f_1875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(v___f_1875_, 0, v___x_1873_);
lean_closure_set(v___f_1875_, 1, v___y_1856_);
lean_closure_set(v___f_1875_, 2, v___y_1852_);
lean_closure_set(v___f_1875_, 3, v_op_1737_);
lean_closure_set(v___f_1875_, 4, v_snd_1859_);
lean_closure_set(v___f_1875_, 5, v___y_1851_);
lean_closure_set(v___f_1875_, 6, v___y_1854_);
lean_closure_set(v___f_1875_, 7, v___y_1853_);
lean_closure_set(v___f_1875_, 8, v_fst_1858_);
lean_closure_set(v___f_1875_, 9, v___x_1874_);
v___x_1876_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1876_, v___f_1875_, v___y_1860_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_toCold_1878_; lean_object* v_options_1879_; uint8_t v_hasTrace_1880_; 
lean_dec_ref_known(v___x_1877_, 1);
v_toCold_1878_ = lean_ctor_get(v___y_1868_, 0);
v_options_1879_ = lean_ctor_get(v_toCold_1878_, 2);
v_hasTrace_1880_ = lean_ctor_get_uint8(v_options_1879_, sizeof(void*)*1);
if (v_hasTrace_1880_ == 0)
{
lean_dec(v___y_1857_);
lean_dec(v___y_1854_);
lean_dec_ref(v_op_1737_);
v___y_1754_ = v___x_1873_;
v___y_1755_ = v_snd_1859_;
v___y_1756_ = v___y_1860_;
v___y_1757_ = v___y_1861_;
v___y_1758_ = v___y_1862_;
v___y_1759_ = v___y_1863_;
v___y_1760_ = v___y_1864_;
v___y_1761_ = v___y_1865_;
v___y_1762_ = v___y_1866_;
v___y_1763_ = v___y_1867_;
v___y_1764_ = v___y_1868_;
v___y_1765_ = v___y_1869_;
goto v___jp_1753_;
}
else
{
lean_object* v_inheritedTraceOptions_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_inheritedTraceOptions_1881_ = lean_ctor_get(v_toCold_1878_, 11);
v___x_1882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1881_, v_options_1879_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_dec(v___y_1857_);
lean_dec(v___y_1854_);
lean_dec_ref(v_op_1737_);
v___y_1754_ = v___x_1873_;
v___y_1755_ = v_snd_1859_;
v___y_1756_ = v___y_1860_;
v___y_1757_ = v___y_1861_;
v___y_1758_ = v___y_1862_;
v___y_1759_ = v___y_1863_;
v___y_1760_ = v___y_1864_;
v___y_1761_ = v___y_1865_;
v___y_1762_ = v___y_1866_;
v___y_1763_ = v___y_1867_;
v___y_1764_ = v___y_1868_;
v___y_1765_ = v___y_1869_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1885_ = l_Lean_MessageData_ofExpr(v_op_1737_);
v___x_1886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
if (lean_obj_tag(v___y_1857_) == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1827_ = v___y_1860_;
v___y_1828_ = v___y_1868_;
v___y_1829_ = v___x_1873_;
v___y_1830_ = v___y_1865_;
v___y_1831_ = v___y_1867_;
v___y_1832_ = v___x_1887_;
v___y_1833_ = v___y_1863_;
v___y_1834_ = v___y_1862_;
v___y_1835_ = v_snd_1859_;
v___y_1836_ = v___x_1882_;
v___y_1837_ = v___y_1869_;
v___y_1838_ = v___y_1864_;
v___y_1839_ = v___y_1861_;
v___y_1840_ = v___y_1854_;
v___y_1841_ = v___y_1866_;
v___y_1842_ = v___x_1888_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1889_; 
lean_dec_ref_known(v___y_1857_, 1);
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1827_ = v___y_1860_;
v___y_1828_ = v___y_1868_;
v___y_1829_ = v___x_1873_;
v___y_1830_ = v___y_1865_;
v___y_1831_ = v___y_1867_;
v___y_1832_ = v___x_1887_;
v___y_1833_ = v___y_1863_;
v___y_1834_ = v___y_1862_;
v___y_1835_ = v_snd_1859_;
v___y_1836_ = v___x_1882_;
v___y_1837_ = v___y_1869_;
v___y_1838_ = v___y_1864_;
v___y_1839_ = v___y_1861_;
v___y_1840_ = v___y_1854_;
v___y_1841_ = v___y_1866_;
v___y_1842_ = v___x_1889_;
goto v___jp_1826_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_snd_1859_);
lean_dec(v___y_1857_);
lean_dec(v___y_1854_);
lean_dec_ref(v_op_1737_);
v_a_1890_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1877_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1877_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_snd_1859_);
lean_dec(v_fst_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec_ref(v_op_1737_);
v_a_1898_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1870_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1870_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
v___jp_1907_:
{
lean_object* v___x_1918_; 
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc_ref(v_op_1737_);
v___x_1918_ = lean_infer_type(v_op_1737_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
v___x_1920_ = lean_whnf(v_a_1919_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_2152_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_2152_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_2152_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
if (lean_obj_tag(v_a_1921_) == 7)
{
lean_object* v_binderType_1925_; lean_object* v_body_1926_; uint8_t v___x_1927_; 
v_binderType_1925_ = lean_ctor_get(v_a_1921_, 1);
lean_inc_ref(v_binderType_1925_);
v_body_1926_ = lean_ctor_get(v_a_1921_, 2);
lean_inc_ref(v_body_1926_);
lean_dec_ref_known(v_a_1921_, 3);
v___x_1927_ = l_Lean_Expr_hasLooseBVars(v_body_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; 
lean_del_object(v___x_1923_);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
v___x_1928_ = lean_whnf(v_body_1926_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_2135_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_2135_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_2135_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_a_1929_) == 7)
{
lean_object* v_binderType_1933_; lean_object* v_body_1934_; uint8_t v___x_1935_; 
v_binderType_1933_ = lean_ctor_get(v_a_1929_, 1);
lean_inc_ref(v_binderType_1933_);
v_body_1934_ = lean_ctor_get(v_a_1929_, 2);
lean_inc_ref(v_body_1934_);
lean_dec_ref_known(v_a_1929_, 3);
v___x_1935_ = l_Lean_Expr_hasLooseBVars(v_body_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_del_object(v___x_1931_);
lean_inc_ref(v_binderType_1925_);
v___x_1936_ = l_Lean_Meta_isExprDefEq(v_binderType_1925_, v_binderType_1933_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2118_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_2118_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2118_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_1942_ = lean_box(0);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
else
{
lean_object* v___x_1946_; 
lean_del_object(v___x_1939_);
lean_inc_ref(v_binderType_1925_);
v___x_1946_ = l_Lean_Meta_isExprDefEq(v_binderType_1925_, v_body_1934_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2109_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_2109_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2109_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_1952_ = lean_box(0);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
else
{
lean_object* v___x_1956_; 
lean_del_object(v___x_1949_);
v___x_1956_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_1737_, v_f_1906_, v___y_1910_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec_ref(v_f_1906_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2100_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2100_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2100_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_unbox(v_a_1957_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_del_object(v___x_1959_);
lean_inc_ref(v_binderType_1925_);
v___x_1962_ = l_Lean_Meta_getLevel(v_binderType_1925_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc_n(v_a_1963_, 2);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21));
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1963_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
lean_inc_ref(v___x_1966_);
v___x_1967_ = l_Lean_mkConst(v___x_1964_, v___x_1966_);
lean_inc_ref(v_op_1737_);
lean_inc_ref(v_binderType_1925_);
v___x_1968_ = l_Lean_mkAppB(v___x_1967_, v_binderType_1925_, v_op_1737_);
v___x_1969_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1968_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2079_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2079_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2079_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_object* v_val_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_1972_);
v_val_1974_ = lean_ctor_get(v_a_1970_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_1970_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_1976_ = v_a_1970_;
v_isShared_1977_ = v_isSharedCheck_2074_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_val_1974_);
lean_dec(v_a_1970_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2074_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23));
lean_inc_ref(v___x_1966_);
v___x_1979_ = l_Lean_mkConst(v___x_1978_, v___x_1966_);
lean_inc_ref(v_op_1737_);
lean_inc_ref(v_binderType_1925_);
v___x_1980_ = l_Lean_mkAppB(v___x_1979_, v_binderType_1925_, v_op_1737_);
v___x_1981_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1980_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25));
lean_inc_ref(v___x_1966_);
v___x_1984_ = l_Lean_mkConst(v___x_1983_, v___x_1966_);
lean_inc_ref(v_op_1737_);
lean_inc_ref(v_binderType_1925_);
v___x_1985_ = l_Lean_mkAppB(v___x_1984_, v_binderType_1925_, v_op_1737_);
v___x_1986_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1985_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
lean_inc_ref(v_binderType_1925_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_binderType_1925_);
v___x_1989_ = v___x_1976_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_binderType_1925_);
v___x_1989_ = v_reuseFailAlloc_2057_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = 0;
v___x_1991_ = lean_box(0);
v___x_1992_ = l_Lean_Meta_mkFreshExprMVar(v___x_1989_, v___x_1990_, v___x_1991_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_n(v_a_1993_, 2);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27));
v___x_1995_ = l_Lean_mkConst(v___x_1994_, v___x_1966_);
lean_inc_ref(v_op_1737_);
lean_inc_ref(v_binderType_1925_);
v___x_1996_ = l_Lean_mkApp3(v___x_1995_, v_binderType_1925_, v_op_1737_, v_a_1993_);
v___x_1997_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1996_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
if (lean_obj_tag(v_a_1998_) == 1)
{
lean_object* v___x_1999_; lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2038_; 
v___x_1999_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_1993_, v___y_1915_);
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2038_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2038_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_2000_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_1737_, v___y_1908_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = lean_box(0);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc(v_a_2005_);
v___x_2009_ = lean_grind_internalize(v_a_2005_, v_a_2007_, v___x_2008_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref_known(v___x_2009_, 1);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 0, v_a_2005_);
v___x_2011_ = v___x_2002_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2005_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
lean_inc(v_a_1982_);
v___y_1851_ = v_val_1974_;
v___y_1852_ = v_a_1963_;
v___y_1853_ = v_a_1982_;
v___y_1854_ = v_a_1987_;
v___y_1855_ = v___x_2012_;
v___y_1856_ = v_binderType_1925_;
v___y_1857_ = v_a_1982_;
v_fst_1858_ = v_a_1998_;
v_snd_1859_ = v___x_2011_;
v___y_1860_ = v___y_1908_;
v___y_1861_ = v___y_1909_;
v___y_1862_ = v___y_1910_;
v___y_1863_ = v___y_1911_;
v___y_1864_ = v___y_1912_;
v___y_1865_ = v___y_1913_;
v___y_1866_ = v___y_1914_;
v___y_1867_ = v___y_1915_;
v___y_1868_ = v___y_1916_;
v___y_1869_ = v___y_1917_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_a_2005_);
lean_del_object(v___x_2002_);
lean_dec_ref_known(v_a_1998_, 1);
lean_dec(v_a_1987_);
lean_dec(v_a_1982_);
lean_dec(v_val_1974_);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2014_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2009_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2009_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_2005_);
lean_del_object(v___x_2002_);
lean_dec_ref_known(v_a_1998_, 1);
lean_dec(v_a_1987_);
lean_dec(v_a_1982_);
lean_dec(v_val_1974_);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2022_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2006_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2006_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_del_object(v___x_2002_);
lean_dec_ref_known(v_a_1998_, 1);
lean_dec(v_a_1987_);
lean_dec(v_a_1982_);
lean_dec(v_val_1974_);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2030_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2004_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2004_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
lean_dec(v_a_1998_);
lean_dec(v_a_1993_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
lean_inc(v_a_1982_);
v___y_1851_ = v_val_1974_;
v___y_1852_ = v_a_1963_;
v___y_1853_ = v_a_1982_;
v___y_1854_ = v_a_1987_;
v___y_1855_ = v___x_2040_;
v___y_1856_ = v_binderType_1925_;
v___y_1857_ = v_a_1982_;
v_fst_1858_ = v___x_2039_;
v_snd_1859_ = v___x_2039_;
v___y_1860_ = v___y_1908_;
v___y_1861_ = v___y_1909_;
v___y_1862_ = v___y_1910_;
v___y_1863_ = v___y_1911_;
v___y_1864_ = v___y_1912_;
v___y_1865_ = v___y_1913_;
v___y_1866_ = v___y_1914_;
v___y_1867_ = v___y_1915_;
v___y_1868_ = v___y_1916_;
v___y_1869_ = v___y_1917_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_1993_);
lean_dec(v_a_1987_);
lean_dec(v_a_1982_);
lean_dec(v_val_1974_);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2041_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1997_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1997_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_1987_);
lean_dec(v_a_1982_);
lean_dec(v_val_1974_);
lean_dec_ref_known(v___x_1966_, 2);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2049_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_1992_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_1992_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_1982_);
lean_del_object(v___x_1976_);
lean_dec(v_val_1974_);
lean_dec_ref_known(v___x_1966_, 2);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2058_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1986_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1986_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1976_);
lean_dec(v_val_1974_);
lean_dec_ref_known(v___x_1966_, 2);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2066_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1981_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1981_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec(v_a_1970_);
lean_dec_ref_known(v___x_1966_, 2);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v___x_2075_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2075_);
v___x_2077_ = v___x_1972_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref_known(v___x_1966_, 2);
lean_dec(v_a_1963_);
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2080_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_1969_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_1969_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2088_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_1962_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_1962_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
lean_dec(v_a_1957_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v___x_2096_ = lean_box(0);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_2096_);
v___x_2098_ = v___x_1959_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_op_1737_);
v_a_2101_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_1956_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_1956_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v_a_2110_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_1946_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_1946_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v_a_2119_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_1936_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_1936_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_2127_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_2127_);
v___x_2129_ = v___x_1931_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec(v_a_1929_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_2131_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_2131_);
v___x_2133_ = v___x_1931_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v_a_2136_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_1928_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_1928_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec_ref(v_body_1926_);
lean_dec_ref(v_binderType_1925_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_2144_ = lean_box(0);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_2144_);
v___x_2146_ = v___x_1923_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_a_1921_);
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v___x_2148_ = lean_box(0);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_2148_);
v___x_2150_ = v___x_1923_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v_a_2153_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_1920_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_1920_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v_f_1906_);
lean_dec_ref(v_op_1737_);
v_a_2161_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_1918_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_1918_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* v_op_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec(v_a_2175_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* v_cls_2187_, lean_object* v_msg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_2187_, v_msg_2188_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* v_cls_2201_, lean_object* v_msg_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2201_, v_msg_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec(v___y_2203_);
return v_res_2214_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* v_00_u03b2_2215_, lean_object* v_m_2216_, lean_object* v_a_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_2216_, v_a_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_2219_, lean_object* v_m_2220_, lean_object* v_a_2221_){
_start:
{
uint8_t v_res_2222_; lean_object* v_r_2223_; 
v_res_2222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_2219_, v_m_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_m_2220_);
v_r_2223_ = lean_box(v_res_2222_);
return v_r_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* v_op_2224_, lean_object* v_a_2225_, lean_object* v_s_2226_){
_start:
{
lean_object* v_structs_2227_; lean_object* v_opIdOf_2228_; lean_object* v_exprToOpIds_2229_; lean_object* v_steps_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_structs_2227_ = lean_ctor_get(v_s_2226_, 0);
v_opIdOf_2228_ = lean_ctor_get(v_s_2226_, 1);
v_exprToOpIds_2229_ = lean_ctor_get(v_s_2226_, 2);
v_steps_2230_ = lean_ctor_get(v_s_2226_, 3);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_s_2226_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v_s_2226_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_steps_2230_);
lean_inc(v_exprToOpIds_2229_);
lean_inc(v_opIdOf_2228_);
lean_inc(v_structs_2227_);
lean_dec(v_s_2226_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_2228_, v_op_2224_, v_a_2225_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_structs_2227_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_exprToOpIds_2229_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_steps_2230_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* v_op_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2240_, v_a_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2283_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2283_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2283_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_opIdOf_2256_; lean_object* v___x_2257_; 
v_opIdOf_2256_ = lean_ctor_get(v_a_2252_, 1);
lean_inc_ref(v_opIdOf_2256_);
lean_dec(v_a_2252_);
v___x_2257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_2256_, v_op_2239_);
lean_dec_ref(v_opIdOf_2256_);
if (lean_obj_tag(v___x_2257_) == 1)
{
lean_object* v_val_2258_; lean_object* v___x_2260_; 
lean_dec_ref(v_op_2239_);
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v___x_2257_, 1);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_val_2258_);
v___x_2260_ = v___x_2254_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_val_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
else
{
lean_object* v___x_2262_; 
lean_dec(v___x_2257_);
lean_del_object(v___x_2254_);
lean_inc_ref(v_op_2239_);
v___x_2262_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_n(v_a_2263_, 2);
lean_dec_ref_known(v___x_2262_, 1);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2264_, 0, v_op_2239_);
lean_closure_set(v___f_2264_, 1, v_a_2263_);
v___x_2265_ = l_Lean_Meta_Grind_AC_acExt;
v___x_2266_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2265_, v___f_2264_, v_a_2240_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; 
v_unused_2274_ = lean_ctor_get(v___x_2266_, 0);
lean_dec(v_unused_2274_);
v___x_2268_ = v___x_2266_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v___x_2266_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v_a_2263_);
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2263_);
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
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_a_2263_);
v_a_2275_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2266_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2266_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_dec_ref(v_op_2239_);
return v___x_2262_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_op_2239_);
v_a_2284_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2251_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2251_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* v_op_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec(v_a_2293_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
uint8_t v___y_2319_; uint8_t v___x_2352_; 
v___x_2352_ = l_Lean_Expr_isApp(v_e_2305_);
if (v___x_2352_ == 0)
{
v___y_2319_ = v___x_2352_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = l_Lean_Expr_appFn_x21(v_e_2305_);
v___x_2354_ = l_Lean_Expr_isApp(v___x_2353_);
lean_dec_ref(v___x_2353_);
v___y_2319_ = v___x_2354_;
goto v___jp_2318_;
}
v___jp_2318_:
{
if (v___y_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Meta_Grind_AC_getOp(v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2343_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2327_ = l_Lean_Expr_appFn_x21(v_e_2305_);
v___x_2328_ = l_Lean_Expr_appFn_x21(v___x_2327_);
v___x_2329_ = lean_ptr_addr(v___x_2328_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_ptr_addr(v_a_2323_);
lean_dec(v_a_2323_);
v___x_2331_ = lean_usize_dec_eq(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
lean_dec_ref(v___x_2327_);
v___x_2332_ = lean_box(0);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2332_);
v___x_2334_ = v___x_2325_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2336_ = l_Lean_Expr_appArg_x21(v___x_2327_);
lean_dec_ref(v___x_2327_);
v___x_2337_ = l_Lean_Expr_appArg_x21(v_e_2305_);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2339_);
v___x_2341_ = v___x_2325_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2322_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2322_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* v_e_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_e_2355_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2397_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2397_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2397_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_commInst_x3f_2386_; 
v_commInst_x3f_2386_ = lean_ctor_get(v_a_2382_, 7);
lean_inc(v_commInst_x3f_2386_);
lean_dec(v_a_2382_);
if (lean_obj_tag(v_commInst_x3f_2386_) == 0)
{
uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2387_ = 0;
v___x_2388_ = lean_box(v___x_2387_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2388_);
v___x_2390_ = v___x_2384_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
else
{
uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_dec_ref_known(v_commInst_x3f_2386_, 1);
v___x_2392_ = 1;
v___x_2393_ = lean_box(v___x_2392_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2393_);
v___x_2395_ = v___x_2384_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2381_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2381_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec(v_a_2406_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2447_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2447_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2447_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v_neutralInst_x3f_2436_; 
v_neutralInst_x3f_2436_ = lean_ctor_get(v_a_2432_, 8);
lean_inc(v_neutralInst_x3f_2436_);
lean_dec(v_a_2432_);
if (lean_obj_tag(v_neutralInst_x3f_2436_) == 0)
{
uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = 0;
v___x_2438_ = lean_box(v___x_2437_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2438_);
v___x_2440_ = v___x_2434_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
else
{
uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_dec_ref_known(v_neutralInst_x3f_2436_, 1);
v___x_2442_ = 1;
v___x_2443_ = lean_box(v___x_2442_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2443_);
v___x_2445_ = v___x_2434_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2431_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2431_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec(v_a_2456_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2497_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2497_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2497_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_idempotentInst_x3f_2486_; 
v_idempotentInst_x3f_2486_ = lean_ctor_get(v_a_2482_, 6);
lean_inc(v_idempotentInst_x3f_2486_);
lean_dec(v_a_2482_);
if (lean_obj_tag(v_idempotentInst_x3f_2486_) == 0)
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2487_ = 0;
v___x_2488_ = lean_box(v___x_2487_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2488_);
v___x_2490_ = v___x_2484_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
else
{
uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
lean_dec_ref_known(v_idempotentInst_x3f_2486_, 1);
v___x_2492_ = 1;
v___x_2493_ = lean_box(v___x_2492_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2493_);
v___x_2495_ = v___x_2484_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2481_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2481_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec(v_a_2506_);
return v_res_2518_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc = _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
}
#ifdef __cplusplus
}
#endif
