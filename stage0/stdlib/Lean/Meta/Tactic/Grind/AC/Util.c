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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_AC_acExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__29_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_285_; lean_object* v_env_286_; lean_object* v___x_287_; lean_object* v_mctx_288_; lean_object* v_lctx_289_; lean_object* v_options_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_285_ = lean_st_ref_get(v___y_283_);
v_env_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_ref(v_env_286_);
lean_dec(v___x_285_);
v___x_287_ = lean_st_ref_get(v___y_281_);
v_mctx_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_mctx_288_);
lean_dec(v___x_287_);
v_lctx_289_ = lean_ctor_get(v___y_280_, 2);
v_options_290_ = lean_ctor_get(v___y_282_, 2);
lean_inc_ref(v_options_290_);
lean_inc_ref(v_lctx_289_);
v___x_291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_291_, 0, v_env_286_);
lean_ctor_set(v___x_291_, 1, v_mctx_288_);
lean_ctor_set(v___x_291_, 2, v_lctx_289_);
lean_ctor_set(v___x_291_, 3, v_options_290_);
v___x_292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_msgData_279_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object* v_msg_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_ref_307_; lean_object* v___x_308_; lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
v_ref_307_ = lean_ctor_get(v___y_304_, 5);
v___x_308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
lean_inc(v_ref_307_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_ref_307_);
lean_ctor_set(v___x_313_, 1, v_a_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 1);
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_324_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_329_, v_a_337_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_354_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_354_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_354_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_structs_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_structs_345_ = lean_ctor_get(v_a_341_, 0);
lean_inc_ref(v_structs_345_);
lean_dec(v_a_341_);
v___x_346_ = lean_array_get_size(v_structs_345_);
v___x_347_ = lean_nat_dec_lt(v_a_328_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref(v_structs_345_);
lean_del_object(v___x_343_);
v___x_348_ = lean_obj_once(&l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1, &l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1);
v___x_349_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v___x_348_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_array_fget(v_structs_345_, v_a_328_);
lean_dec_ref(v_structs_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_350_);
v___x_352_ = v___x_343_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
v_a_355_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_340_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_340_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_377_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(v_00_u03b1_391_, v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
lean_dec(v___y_393_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object* v_a_407_, lean_object* v_f_408_, lean_object* v_s_409_){
_start:
{
lean_object* v_structs_410_; lean_object* v_opIdOf_411_; lean_object* v_exprToOpIds_412_; lean_object* v_steps_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_structs_410_ = lean_ctor_get(v_s_409_, 0);
v_opIdOf_411_ = lean_ctor_get(v_s_409_, 1);
v_exprToOpIds_412_ = lean_ctor_get(v_s_409_, 2);
v_steps_413_ = lean_ctor_get(v_s_409_, 3);
v___x_414_ = lean_array_get_size(v_structs_410_);
v___x_415_ = lean_nat_dec_lt(v_a_407_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec_ref(v_f_408_);
return v_s_409_;
}
else
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_427_; 
lean_inc(v_steps_413_);
lean_inc_ref(v_exprToOpIds_412_);
lean_inc_ref(v_opIdOf_411_);
lean_inc_ref(v_structs_410_);
v_isSharedCheck_427_ = !lean_is_exclusive(v_s_409_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_428_ = lean_ctor_get(v_s_409_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_s_409_, 2);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_s_409_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_s_409_, 0);
lean_dec(v_unused_431_);
v___x_417_ = v_s_409_;
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_s_409_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_v_419_; lean_object* v___x_420_; lean_object* v_xs_x27_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v_v_419_ = lean_array_fget(v_structs_410_, v_a_407_);
v___x_420_ = lean_box(0);
v_xs_x27_421_ = lean_array_fset(v_structs_410_, v_a_407_, v___x_420_);
v___x_422_ = lean_apply_1(v_f_408_, v_v_419_);
v___x_423_ = lean_array_fset(v_xs_x27_421_, v_a_407_, v___x_422_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_423_);
v___x_425_ = v___x_417_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_opIdOf_411_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_exprToOpIds_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_steps_413_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_432_, lean_object* v_f_433_, lean_object* v_s_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(v_a_432_, v_f_433_, v_s_434_);
lean_dec(v_a_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object* v_f_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc(v_a_437_);
v___f_440_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_440_, 0, v_a_437_);
lean_closure_set(v___f_440_, 1, v_f_436_);
v___x_441_ = l_Lean_Meta_Grind_AC_acExt;
v___x_442_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_441_, v___f_440_, v_a_438_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object* v_f_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec(v_a_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object* v_f_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_448_, v_a_449_, v_a_450_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object* v_f_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Grind_AC_modifyStruct(v_f_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_497_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_497_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_op_493_; lean_object* v___x_495_; 
v_op_493_ = lean_ctor_get(v_a_489_, 3);
lean_inc_ref(v_op_493_);
lean_dec(v_a_489_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_op_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_op_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_488_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_Grind_AC_getOp(v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object* v_m_519_, lean_object* v_query_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_zero_524_; uint8_t v_isZero_525_; 
v_zero_524_ = lean_unsigned_to_nat(0u);
v_isZero_525_ = lean_nat_dec_eq(v_x_522_, v_zero_524_);
if (v_isZero_525_ == 1)
{
lean_dec(v_x_523_);
lean_dec(v_x_522_);
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(2);
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_val_527_ = lean_ctor_get(v_x_521_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v_x_521_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v_x_521_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_val_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_keyArray_535_; lean_object* v_valueArray_536_; lean_object* v___x_537_; uint8_t v_isSome_538_; 
v_keyArray_535_ = lean_ctor_get(v_m_519_, 1);
v_valueArray_536_ = lean_ctor_get(v_m_519_, 2);
v___x_537_ = lean_array_fget_borrowed(v_keyArray_535_, v_x_523_);
v_isSome_538_ = lean_noption_is_some(v___x_537_);
if (v_isSome_538_ == 0)
{
lean_dec(v_x_522_);
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_x_523_);
return v___x_539_;
}
else
{
lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_x_523_);
v_val_540_ = lean_ctor_get(v_x_521_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_x_521_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v_x_521_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_dec(v_x_521_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_val_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_one_548_; lean_object* v_n_549_; lean_object* v___y_551_; 
v_one_548_ = lean_unsigned_to_nat(1u);
v_n_549_ = lean_nat_sub(v_x_522_, v_one_548_);
lean_dec(v_x_522_);
if (v_isSome_538_ == 0)
{
goto v___jp_557_;
}
else
{
lean_object* v___x_559_; uint8_t v_isSome_560_; 
v___x_559_ = lean_array_fget_borrowed(v_valueArray_536_, v_x_523_);
v_isSome_560_ = lean_noption_is_some(v___x_559_);
if (v_isSome_560_ == 0)
{
goto v___jp_557_;
}
else
{
lean_object* v_val_561_; uint8_t v___x_562_; 
lean_inc(v___x_537_);
v_val_561_ = lean_noption_get(v___x_537_);
v___x_562_ = lean_name_eq(v_val_561_, v_query_520_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
lean_dec(v_val_561_);
v___x_563_ = lean_array_get_size(v_keyArray_535_);
v___x_564_ = lean_nat_add(v_x_523_, v_one_548_);
lean_dec(v_x_523_);
v___x_565_ = lean_nat_dec_lt(v___x_564_, v___x_563_);
if (v___x_565_ == 0)
{
lean_dec(v___x_564_);
v_x_522_ = v_n_549_;
v_x_523_ = v_zero_524_;
goto _start;
}
else
{
v_x_522_ = v_n_549_;
v_x_523_ = v___x_564_;
goto _start;
}
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; 
lean_dec(v_n_549_);
lean_dec(v_x_521_);
lean_inc(v___x_559_);
v_val_568_ = lean_noption_get(v___x_559_);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v_x_523_);
lean_ctor_set(v___x_569_, 1, v_val_561_);
lean_ctor_set(v___x_569_, 2, v_val_568_);
return v___x_569_;
}
}
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_array_get_size(v_keyArray_535_);
v___x_553_ = lean_nat_add(v_x_523_, v_one_548_);
lean_dec(v_x_523_);
v___x_554_ = lean_nat_dec_lt(v___x_553_, v___x_552_);
if (v___x_554_ == 0)
{
lean_dec(v___x_553_);
v_x_521_ = v___y_551_;
v_x_522_ = v_n_549_;
v_x_523_ = v_zero_524_;
goto _start;
}
else
{
v_x_521_ = v___y_551_;
v_x_522_ = v_n_549_;
v_x_523_ = v___x_553_;
goto _start;
}
}
v___jp_557_:
{
if (lean_obj_tag(v_x_521_) == 0)
{
lean_object* v___x_558_; 
lean_inc(v_x_523_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_x_523_);
v___y_551_ = v___x_558_;
goto v___jp_550_;
}
else
{
v___y_551_ = v_x_521_;
goto v___jp_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_570_, lean_object* v_query_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_m_570_, v_query_571_, v_x_572_, v_x_573_, v_x_574_);
lean_dec(v_query_571_);
lean_dec_ref(v_m_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object* v_m_576_, lean_object* v_query_577_){
_start:
{
lean_object* v_keyArray_578_; lean_object* v___x_579_; uint64_t v___y_581_; 
v_keyArray_578_ = lean_ctor_get(v_m_576_, 1);
v___x_579_ = lean_array_get_size(v_keyArray_578_);
if (lean_obj_tag(v_query_577_) == 0)
{
uint64_t v___x_596_; 
v___x_596_ = 1723ULL;
v___y_581_ = v___x_596_;
goto v___jp_580_;
}
else
{
uint64_t v_hash_597_; 
v_hash_597_ = lean_ctor_get_uint64(v_query_577_, sizeof(void*)*2);
v___y_581_ = v_hash_597_;
goto v___jp_580_;
}
v___jp_580_:
{
uint64_t v___x_582_; uint64_t v___x_583_; uint64_t v_fold_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_582_ = 32ULL;
v___x_583_ = lean_uint64_shift_right(v___y_581_, v___x_582_);
v_fold_584_ = lean_uint64_xor(v___y_581_, v___x_583_);
v___x_585_ = 16ULL;
v___x_586_ = lean_uint64_shift_right(v_fold_584_, v___x_585_);
v___x_587_ = lean_uint64_xor(v_fold_584_, v___x_586_);
v___x_588_ = lean_uint64_to_usize(v___x_587_);
v___x_589_ = lean_usize_of_nat(v___x_579_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_sub(v___x_589_, v___x_590_);
v___x_592_ = lean_usize_land(v___x_588_, v___x_591_);
v___x_593_ = lean_usize_to_nat(v___x_592_);
v___x_594_ = lean_box(0);
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_m_576_, v_query_577_, v___x_594_, v___x_579_, v___x_593_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg___boxed(lean_object* v_m_598_, lean_object* v_query_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_598_, v_query_599_);
lean_dec(v_query_599_);
lean_dec_ref(v_m_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_b_601_, lean_object* v_acc_602_, lean_object* v_i_603_){
_start:
{
lean_object* v___y_605_; lean_object* v_keyArray_613_; lean_object* v_valueArray_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_keyArray_613_ = lean_ctor_get(v_b_601_, 1);
v_valueArray_614_ = lean_ctor_get(v_b_601_, 2);
v___x_615_ = lean_array_get_size(v_keyArray_613_);
v___x_616_ = lean_nat_dec_lt(v_i_603_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec(v_i_603_);
return v_acc_602_;
}
else
{
lean_object* v___x_617_; uint8_t v_isSome_618_; 
v___x_617_ = lean_array_fget_borrowed(v_keyArray_613_, v_i_603_);
v_isSome_618_ = lean_noption_is_some(v___x_617_);
if (v_isSome_618_ == 0)
{
goto v___jp_609_;
}
else
{
lean_object* v___x_619_; uint8_t v_isSome_620_; 
v___x_619_ = lean_array_fget_borrowed(v_valueArray_614_, v_i_603_);
v_isSome_620_ = lean_noption_is_some(v___x_619_);
if (v_isSome_620_ == 0)
{
goto v___jp_609_;
}
else
{
lean_object* v_val_621_; lean_object* v_val_622_; lean_object* v_i_624_; lean_object* v___x_629_; 
lean_inc(v___x_617_);
v_val_621_ = lean_noption_get(v___x_617_);
lean_inc(v___x_619_);
v_val_622_ = lean_noption_get(v___x_619_);
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_acc_602_, v_val_621_);
switch(lean_obj_tag(v___x_629_))
{
case 0:
{
lean_object* v_index_630_; lean_object* v_size_631_; lean_object* v___x_632_; 
v_index_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_index_630_);
lean_dec_ref_known(v___x_629_, 3);
v_size_631_ = lean_ctor_get(v_acc_602_, 0);
lean_inc(v_size_631_);
v___x_632_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_602_, v_size_631_, v_index_630_, v_val_621_, v_val_622_);
lean_dec(v_index_630_);
v___y_605_ = v___x_632_;
goto v___jp_604_;
}
case 1:
{
lean_object* v_index_633_; 
v_index_633_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_index_633_);
lean_dec_ref_known(v___x_629_, 1);
v_i_624_ = v_index_633_;
goto v___jp_623_;
}
default: 
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_602_, v___x_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_index_636_; 
v_index_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_index_636_);
lean_dec_ref_known(v___x_635_, 1);
v_i_624_ = v_index_636_;
goto v___jp_623_;
}
else
{
lean_dec(v_val_622_);
lean_dec(v_val_621_);
v___y_605_ = v_acc_602_;
goto v___jp_604_;
}
}
}
v___jp_623_:
{
lean_object* v_size_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_size_625_ = lean_ctor_get(v_acc_602_, 0);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_size_625_, v___x_626_);
v___x_628_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_602_, v___x_627_, v_i_624_, v_val_621_, v_val_622_);
lean_dec(v_i_624_);
v___y_605_ = v___x_628_;
goto v___jp_604_;
}
}
}
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_i_603_, v___x_606_);
lean_dec(v_i_603_);
v_acc_602_ = v___y_605_;
v_i_603_ = v___x_607_;
goto _start;
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v_i_603_, v___x_610_);
lean_dec(v_i_603_);
v_i_603_ = v___x_611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_b_637_, lean_object* v_acc_638_, lean_object* v_i_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg(v_b_637_, v_acc_638_, v_i_639_);
lean_dec_ref(v_b_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg(lean_object* v_init_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg(v_b_642_, v_init_641_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_init_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg(v_init_645_, v_b_646_);
lean_dec_ref(v_b_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object* v_m_648_){
_start:
{
lean_object* v_keyArray_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_cellCount_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_target_656_; lean_object* v___x_657_; 
v_keyArray_649_ = lean_ctor_get(v_m_648_, 1);
v___x_650_ = lean_array_get_size(v_keyArray_649_);
v___x_651_ = lean_unsigned_to_nat(2u);
v_cellCount_652_ = lean_nat_mul(v___x_650_, v___x_651_);
v___x_653_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_652_);
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_652_);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_652_);
v_target_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_656_, 0, v___x_653_);
lean_ctor_set(v_target_656_, 1, v___x_654_);
lean_ctor_set(v_target_656_, 2, v___x_655_);
v___x_657_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg(v_target_656_, v_m_648_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object* v_m_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_m_658_);
lean_dec_ref(v_m_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(lean_object* v_as_x27_660_, lean_object* v_b_661_){
_start:
{
if (lean_obj_tag(v_as_x27_660_) == 0)
{
return v_b_661_;
}
else
{
lean_object* v_head_662_; lean_object* v_tail_663_; lean_object* v___x_664_; lean_object* v___y_666_; lean_object* v_i_667_; lean_object* v___y_674_; lean_object* v___y_686_; lean_object* v_i_687_; lean_object* v___x_705_; 
v_head_662_ = lean_ctor_get(v_as_x27_660_, 0);
v_tail_663_ = lean_ctor_get(v_as_x27_660_, 1);
v___x_664_ = lean_box(0);
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_661_, v_head_662_);
switch(lean_obj_tag(v___x_705_))
{
case 0:
{
lean_dec_ref_known(v___x_705_, 3);
v_as_x27_660_ = v_tail_663_;
goto _start;
}
case 1:
{
lean_object* v_index_707_; lean_object* v_size_708_; lean_object* v_keyArray_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_index_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_index_707_);
lean_dec_ref_known(v___x_705_, 1);
v_size_708_ = lean_ctor_get(v_b_661_, 0);
v_keyArray_709_ = lean_ctor_get(v_b_661_, 1);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_add(v_size_708_, v___x_710_);
v___x_712_ = lean_array_get_size(v_keyArray_709_);
v___x_713_ = lean_nat_dec_lt(v___x_711_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v___x_711_);
lean_dec(v_index_707_);
goto v___jp_693_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_714_ = lean_unsigned_to_nat(4u);
v___x_715_ = lean_nat_mul(v___x_711_, v___x_714_);
v___x_716_ = lean_unsigned_to_nat(3u);
v___x_717_ = lean_nat_mul(v___x_712_, v___x_716_);
v___x_718_ = lean_nat_dec_le(v___x_715_, v___x_717_);
lean_dec(v___x_717_);
lean_dec(v___x_715_);
if (v___x_718_ == 0)
{
lean_dec(v___x_711_);
lean_dec(v_index_707_);
goto v___jp_693_;
}
else
{
lean_object* v___x_719_; 
lean_inc(v_head_662_);
v___x_719_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_661_, v___x_711_, v_index_707_, v_head_662_, v___x_664_);
lean_dec(v_index_707_);
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_719_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_721_; lean_object* v_keyArray_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_size_721_ = lean_ctor_get(v_b_661_, 0);
v_keyArray_722_ = lean_ctor_get(v_b_661_, 1);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_size_721_, v___x_723_);
v___x_725_ = lean_array_get_size(v_keyArray_722_);
v___x_726_ = lean_nat_dec_lt(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v___x_724_);
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_b_661_);
lean_dec_ref(v_b_661_);
v___y_674_ = v___x_727_;
goto v___jp_673_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_728_ = lean_unsigned_to_nat(4u);
v___x_729_ = lean_nat_mul(v___x_724_, v___x_728_);
lean_dec(v___x_724_);
v___x_730_ = lean_unsigned_to_nat(3u);
v___x_731_ = lean_nat_mul(v___x_725_, v___x_730_);
v___x_732_ = lean_nat_dec_le(v___x_729_, v___x_731_);
lean_dec(v___x_731_);
lean_dec(v___x_729_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_b_661_);
lean_dec_ref(v_b_661_);
v___y_674_ = v___x_733_;
goto v___jp_673_;
}
else
{
v___y_674_ = v_b_661_;
goto v___jp_673_;
}
}
}
}
v___jp_665_:
{
lean_object* v_size_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_size_668_ = lean_ctor_get(v___y_666_, 0);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_size_668_, v___x_669_);
lean_inc(v_head_662_);
v___x_671_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_666_, v___x_670_, v_i_667_, v_head_662_, v___x_664_);
lean_dec(v_i_667_);
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_671_;
goto _start;
}
v___jp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v___y_674_, v_head_662_);
switch(lean_obj_tag(v___x_675_))
{
case 0:
{
lean_object* v_index_676_; lean_object* v_size_677_; lean_object* v___x_678_; 
v_index_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_index_676_);
lean_dec_ref_known(v___x_675_, 3);
v_size_677_ = lean_ctor_get(v___y_674_, 0);
lean_inc(v_size_677_);
lean_inc(v_head_662_);
v___x_678_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_674_, v_size_677_, v_index_676_, v_head_662_, v___x_664_);
lean_dec(v_index_676_);
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_678_;
goto _start;
}
case 1:
{
lean_object* v_index_680_; 
v_index_680_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_index_680_);
lean_dec_ref_known(v___x_675_, 1);
v___y_666_ = v___y_674_;
v_i_667_ = v_index_680_;
goto v___jp_665_;
}
default: 
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_674_, v___x_681_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_index_683_; 
v_index_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_index_683_);
lean_dec_ref_known(v___x_682_, 1);
v___y_666_ = v___y_674_;
v_i_667_ = v_index_683_;
goto v___jp_665_;
}
else
{
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___y_674_;
goto _start;
}
}
}
}
v___jp_685_:
{
lean_object* v_size_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_size_688_ = lean_ctor_get(v___y_686_, 0);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_size_688_, v___x_689_);
lean_inc(v_head_662_);
v___x_691_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_686_, v___x_690_, v_i_687_, v_head_662_, v___x_664_);
lean_dec(v_i_687_);
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_691_;
goto _start;
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_b_661_);
lean_dec_ref(v_b_661_);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v___x_694_, v_head_662_);
switch(lean_obj_tag(v___x_695_))
{
case 0:
{
lean_object* v_index_696_; lean_object* v_size_697_; lean_object* v___x_698_; 
v_index_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_695_, 3);
v_size_697_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_size_697_);
lean_inc(v_head_662_);
v___x_698_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_694_, v_size_697_, v_index_696_, v_head_662_, v___x_664_);
lean_dec(v_index_696_);
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_698_;
goto _start;
}
case 1:
{
lean_object* v_index_700_; 
v_index_700_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_700_);
lean_dec_ref_known(v___x_695_, 1);
v___y_686_ = v___x_694_;
v_i_687_ = v_index_700_;
goto v___jp_685_;
}
default: 
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_694_, v___x_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_index_703_; 
v_index_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_index_703_);
lean_dec_ref_known(v___x_702_, 1);
v___y_686_ = v___x_694_;
v_i_687_ = v_index_703_;
goto v___jp_685_;
}
else
{
v_as_x27_660_ = v_tail_663_;
v_b_661_ = v___x_694_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_734_, lean_object* v_b_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(v_as_x27_734_, v_b_735_);
lean_dec(v_as_x27_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object* v_m_737_, lean_object* v_l_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(v_l_738_, v_m_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(lean_object* v_m_740_, lean_object* v_l_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_740_, v_l_741_);
lean_dec(v_l_741_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37(void){
_start:
{
lean_object* v_cellCount_817_; lean_object* v___x_818_; 
v_cellCount_817_ = lean_unsigned_to_nat(16u);
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_817_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38(void){
_start:
{
lean_object* v_cellCount_819_; lean_object* v___x_820_; 
v_cellCount_819_ = lean_unsigned_to_nat(16u);
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_819_);
return v___x_820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
v___x_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_822_);
lean_ctor_set(v___x_824_, 2, v___x_821_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36));
v___x_827_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc(void){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__40);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_query_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_830_, v_query_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_833_, lean_object* v_m_834_, lean_object* v_query_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(v_00_u03b2_833_, v_m_834_, v_query_835_);
lean_dec(v_query_835_);
lean_dec_ref(v_m_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object* v_00_u03b2_837_, lean_object* v_m_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_m_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object* v_00_u03b2_840_, lean_object* v_m_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_00_u03b2_840_, v_m_841_);
lean_dec_ref(v_m_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2(lean_object* v_as_843_, lean_object* v_as_x27_844_, lean_object* v_b_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___redArg(v_as_x27_844_, v_b_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2___boxed(lean_object* v_as_848_, lean_object* v_as_x27_849_, lean_object* v_b_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__2(v_as_848_, v_as_x27_849_, v_b_850_, v_a_851_);
lean_dec(v_as_x27_849_);
lean_dec(v_as_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_853_, lean_object* v_m_854_, lean_object* v_query_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_m_854_, v_query_855_, v_x_856_, v_x_857_, v_x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_861_, lean_object* v_m_862_, lean_object* v_query_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_861_, v_m_862_, v_query_863_, v_x_864_, v_x_865_, v_x_866_, v_x_867_);
lean_dec(v_query_863_);
lean_dec_ref(v_m_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_869_, lean_object* v_init_870_, lean_object* v_b_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___redArg(v_init_870_, v_b_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_873_, lean_object* v_init_874_, lean_object* v_b_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3(v_00_u03b2_873_, v_init_874_, v_b_875_);
lean_dec_ref(v_b_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_877_, lean_object* v_b_878_, lean_object* v_acc_879_, lean_object* v_i_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___redArg(v_b_878_, v_acc_879_, v_i_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b2_882_, lean_object* v_b_883_, lean_object* v_acc_884_, lean_object* v_i_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1_spec__3_spec__4(v_00_u03b2_882_, v_b_883_, v_acc_884_, v_i_885_);
lean_dec_ref(v_b_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* v_op_912_, lean_object* v_f_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_916_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_1001_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_1001_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_1001_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint8_t v_ring_934_; uint8_t v___y_936_; lean_object* v___y_937_; 
v_ring_934_ = lean_ctor_get_uint8(v_a_930_, sizeof(void*)*14 + 21);
lean_dec(v_a_930_);
if (v_ring_934_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_box(v_ring_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_981_);
v___x_983_ = v___x_932_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
if (lean_obj_tag(v_f_913_) == 4)
{
lean_object* v_declName_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
lean_del_object(v___x_932_);
v_declName_985_ = lean_ctor_get(v_f_913_, 0);
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2));
v___x_987_ = lean_name_eq(v_declName_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5));
v___x_989_ = lean_name_eq(v_declName_985_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8));
v___x_991_ = lean_name_eq(v_declName_985_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11));
v___x_993_ = lean_name_eq(v_declName_985_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14));
v___x_995_ = lean_name_eq(v_declName_985_, v___x_994_);
if (v___x_995_ == 0)
{
goto v___jp_925_;
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
goto v___jp_956_;
}
}
else
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = 0;
v___x_997_ = lean_box(v___x_996_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_997_);
v___x_999_ = v___x_932_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
v___jp_935_:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v___y_937_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_del_object(v___x_941_);
goto v___jp_925_;
}
else
{
lean_dec_ref_known(v_a_939_, 1);
if (v___y_936_ == 0)
{
lean_del_object(v___x_941_);
goto v___jp_925_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_box(v_ring_934_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_938_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_957_ = l_Lean_Expr_getAppNumArgs(v_op_912_);
v___x_958_ = lean_unsigned_to_nat(4u);
v___x_959_ = lean_nat_dec_eq(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
goto v___jp_925_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_Expr_appFn_x21(v_op_912_);
v___x_961_ = l_Lean_Expr_appFn_x21(v___x_960_);
lean_dec_ref(v___x_960_);
v___x_962_ = l_Lean_Expr_appArg_x21(v___x_961_);
lean_dec_ref(v___x_961_);
lean_inc_ref(v___x_962_);
v___x_963_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v___x_962_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_972_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_972_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_972_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
if (lean_obj_tag(v_a_964_) == 0)
{
lean_del_object(v___x_966_);
v___y_936_ = v___x_959_;
v___y_937_ = v___x_962_;
goto v___jp_935_;
}
else
{
lean_dec_ref_known(v_a_964_, 1);
if (v___x_959_ == 0)
{
lean_del_object(v___x_966_);
v___y_936_ = v___x_959_;
v___y_937_ = v___x_962_;
goto v___jp_935_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec_ref(v___x_962_);
v___x_968_ = lean_box(v_ring_934_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v___x_962_);
v_a_973_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_963_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_963_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_929_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_929_);
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
v___jp_925_:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = 0;
v___x_927_ = lean_box(v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* v_op_1010_, lean_object* v_f_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_1010_, v_f_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_f_1011_);
lean_dec_ref(v_op_1010_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1024_, lean_object* v_vals_1025_, lean_object* v_i_1026_, lean_object* v_k_1027_){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_array_get_size(v_keys_1024_);
v___x_1029_ = lean_nat_dec_lt(v_i_1026_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
lean_dec(v_i_1026_);
v___x_1030_ = lean_box(0);
return v___x_1030_;
}
else
{
lean_object* v_k_x27_1031_; size_t v___x_1032_; size_t v___x_1033_; uint8_t v___x_1034_; 
v_k_x27_1031_ = lean_array_fget_borrowed(v_keys_1024_, v_i_1026_);
v___x_1032_ = lean_ptr_addr(v_k_1027_);
v___x_1033_ = lean_ptr_addr(v_k_x27_1031_);
v___x_1034_ = lean_usize_dec_eq(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_nat_add(v_i_1026_, v___x_1035_);
lean_dec(v_i_1026_);
v_i_1026_ = v___x_1036_;
goto _start;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_array_fget_borrowed(v_vals_1025_, v_i_1026_);
lean_dec(v_i_1026_);
lean_inc(v___x_1038_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1040_, lean_object* v_vals_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1040_, v_vals_1041_, v_i_1042_, v_k_1043_);
lean_dec_ref(v_k_1043_);
lean_dec_ref(v_vals_1041_);
lean_dec_ref(v_keys_1040_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* v_x_1045_, size_t v_x_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1045_) == 0)
{
lean_object* v_es_1048_; lean_object* v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v_j_1052_; lean_object* v___x_1053_; 
v_es_1048_ = lean_ctor_get(v_x_1045_, 0);
v___x_1049_ = lean_box(2);
v___x_1050_ = ((size_t)31ULL);
v___x_1051_ = lean_usize_land(v_x_1046_, v___x_1050_);
v_j_1052_ = lean_usize_to_nat(v___x_1051_);
v___x_1053_ = lean_array_get_borrowed(v___x_1049_, v_es_1048_, v_j_1052_);
lean_dec(v_j_1052_);
switch(lean_obj_tag(v___x_1053_))
{
case 0:
{
lean_object* v_key_1054_; lean_object* v_val_1055_; size_t v___x_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v_key_1054_ = lean_ctor_get(v___x_1053_, 0);
v_val_1055_ = lean_ctor_get(v___x_1053_, 1);
v___x_1056_ = lean_ptr_addr(v_x_1047_);
v___x_1057_ = lean_ptr_addr(v_key_1054_);
v___x_1058_ = lean_usize_dec_eq(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_box(0);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; 
lean_inc(v_val_1055_);
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_val_1055_);
return v___x_1060_;
}
}
case 1:
{
lean_object* v_node_1061_; size_t v___x_1062_; size_t v___x_1063_; 
v_node_1061_ = lean_ctor_get(v___x_1053_, 0);
v___x_1062_ = ((size_t)5ULL);
v___x_1063_ = lean_usize_shift_right(v_x_1046_, v___x_1062_);
v_x_1045_ = v_node_1061_;
v_x_1046_ = v___x_1063_;
goto _start;
}
default: 
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
}
}
else
{
lean_object* v_ks_1066_; lean_object* v_vs_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_ks_1066_ = lean_ctor_get(v_x_1045_, 0);
v_vs_1067_ = lean_ctor_get(v_x_1045_, 1);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_1066_, v_vs_1067_, v___x_1068_, v_x_1047_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_972__boxed_1073_; lean_object* v_res_1074_; 
v_x_972__boxed_1073_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1074_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1070_, v_x_972__boxed_1073_, v_x_1072_);
lean_dec_ref(v_x_1072_);
lean_dec_ref(v_x_1070_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; uint64_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1077_ = lean_ptr_addr(v_x_1076_);
v___x_1078_ = ((size_t)3ULL);
v___x_1079_ = lean_usize_shift_right(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_usize_to_uint64(v___x_1079_);
v___x_1081_ = lean_uint64_to_usize(v___x_1080_);
v___x_1082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1075_, v___x_1081_, v_x_1076_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1083_, v_x_1084_);
lean_dec_ref(v_x_1084_);
lean_dec_ref(v_x_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* v_e_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1105_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1105_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1105_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_exprToOpIds_1095_; lean_object* v___x_1096_; 
v_exprToOpIds_1095_ = lean_ctor_get(v_a_1091_, 2);
lean_inc_ref(v_exprToOpIds_1095_);
lean_dec(v_a_1091_);
v___x_1096_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_1095_, v_e_1086_);
lean_dec_ref(v_exprToOpIds_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_box(0);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1097_);
v___x_1099_ = v___x_1093_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v_val_1101_; lean_object* v___x_1103_; 
v_val_1101_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v___x_1096_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_val_1101_);
v___x_1103_ = v___x_1093_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_val_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1090_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1090_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* v_e_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1114_, v_a_1115_, v_a_1116_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_e_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* v_e_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1119_, v_a_1120_, v_a_1128_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* v_e_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_e_1132_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* v_00_u03b2_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1146_, v_x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(v_00_u03b2_1149_, v_x_1150_, v_x_1151_);
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_x_1150_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* v_00_u03b2_1153_, lean_object* v_x_1154_, size_t v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1154_, v_x_1155_, v_x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
size_t v_x_1103__boxed_1162_; lean_object* v_res_1163_; 
v_x_1103__boxed_1162_ = lean_unbox_usize(v_x_1160_);
lean_dec(v_x_1160_);
v_res_1163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_1158_, v_x_1159_, v_x_1103__boxed_1162_, v_x_1161_);
lean_dec_ref(v_x_1161_);
lean_dec_ref(v_x_1159_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1164_, lean_object* v_keys_1165_, lean_object* v_vals_1166_, lean_object* v_heq_1167_, lean_object* v_i_1168_, lean_object* v_k_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1165_, v_vals_1166_, v_i_1168_, v_k_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1171_, lean_object* v_keys_1172_, lean_object* v_vals_1173_, lean_object* v_heq_1174_, lean_object* v_i_1175_, lean_object* v_k_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_1171_, v_keys_1172_, v_vals_1173_, v_heq_1174_, v_i_1175_, v_k_1176_);
lean_dec_ref(v_k_1176_);
lean_dec_ref(v_vals_1173_);
lean_dec_ref(v_keys_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* v_opId_1178_, lean_object* v_a_1179_){
_start:
{
if (lean_obj_tag(v_a_1179_) == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_opId_1178_);
lean_ctor_set(v___x_1180_, 1, v_a_1179_);
return v___x_1180_;
}
else
{
lean_object* v_head_1181_; lean_object* v_tail_1182_; uint8_t v___x_1183_; 
v_head_1181_ = lean_ctor_get(v_a_1179_, 0);
v_tail_1182_ = lean_ctor_get(v_a_1179_, 1);
v___x_1183_ = lean_nat_dec_lt(v_opId_1178_, v_head_1181_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1195_; 
lean_inc(v_tail_1182_);
lean_inc(v_head_1181_);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; lean_object* v_unused_1197_; 
v_unused_1196_ = lean_ctor_get(v_a_1179_, 1);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_a_1179_, 0);
lean_dec(v_unused_1197_);
v___x_1185_ = v_a_1179_;
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_a_1179_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_nat_dec_eq(v_opId_1178_, v_head_1181_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1178_, v_tail_1182_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_head_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
else
{
lean_object* v___x_1193_; 
lean_dec(v_head_1181_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_opId_1178_);
v___x_1193_ = v___x_1185_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_opId_1178_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_tail_1182_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_opId_1178_);
lean_ctor_set(v___x_1198_, 1, v_a_1179_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v_ks_1203_; lean_object* v_vs_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1230_; 
v_ks_1203_ = lean_ctor_get(v_x_1199_, 0);
v_vs_1204_ = lean_ctor_get(v_x_1199_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1206_ = v_x_1199_;
v_isShared_1207_ = v_isSharedCheck_1230_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_vs_1204_);
lean_inc(v_ks_1203_);
lean_dec(v_x_1199_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1230_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_array_get_size(v_ks_1203_);
v___x_1209_ = lean_nat_dec_lt(v_x_1200_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_dec(v_x_1200_);
v___x_1210_ = lean_array_push(v_ks_1203_, v_x_1201_);
v___x_1211_ = lean_array_push(v_vs_1204_, v_x_1202_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1211_);
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v_k_x27_1215_; size_t v___x_1216_; size_t v___x_1217_; uint8_t v___x_1218_; 
v_k_x27_1215_ = lean_array_fget_borrowed(v_ks_1203_, v_x_1200_);
v___x_1216_ = lean_ptr_addr(v_x_1201_);
v___x_1217_ = lean_ptr_addr(v_k_x27_1215_);
v___x_1218_ = lean_usize_dec_eq(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1220_; 
if (v_isShared_1207_ == 0)
{
v___x_1220_ = v___x_1206_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_ks_1203_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_vs_1204_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_x_1200_, v___x_1221_);
lean_dec(v_x_1200_);
v_x_1199_ = v___x_1220_;
v_x_1200_ = v___x_1222_;
goto _start;
}
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = lean_array_fset(v_ks_1203_, v_x_1200_, v_x_1201_);
v___x_1226_ = lean_array_fset(v_vs_1204_, v_x_1200_, v_x_1202_);
lean_dec(v_x_1200_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1226_);
lean_ctor_set(v___x_1206_, 0, v___x_1225_);
v___x_1228_ = v___x_1206_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1231_, lean_object* v_k_1232_, lean_object* v_v_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1231_, v___x_1234_, v_k_1232_, v_v_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* v_x_1237_, size_t v_x_1238_, size_t v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 0)
{
lean_object* v_es_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v_j_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_es_1242_ = lean_ctor_get(v_x_1237_, 0);
v___x_1243_ = ((size_t)31ULL);
v___x_1244_ = lean_usize_land(v_x_1238_, v___x_1243_);
v_j_1245_ = lean_usize_to_nat(v___x_1244_);
v___x_1246_ = lean_array_get_size(v_es_1242_);
v___x_1247_ = lean_nat_dec_lt(v_j_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v_j_1245_);
lean_dec(v_x_1241_);
lean_dec_ref(v_x_1240_);
return v_x_1237_;
}
else
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1288_; 
lean_inc_ref(v_es_1242_);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_x_1237_, 0);
lean_dec(v_unused_1289_);
v___x_1249_ = v_x_1237_;
v_isShared_1250_ = v_isSharedCheck_1288_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v_x_1237_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1288_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_v_1251_; lean_object* v___x_1252_; lean_object* v_xs_x27_1253_; lean_object* v___y_1255_; 
v_v_1251_ = lean_array_fget(v_es_1242_, v_j_1245_);
v___x_1252_ = lean_box(0);
v_xs_x27_1253_ = lean_array_fset(v_es_1242_, v_j_1245_, v___x_1252_);
switch(lean_obj_tag(v_v_1251_))
{
case 0:
{
lean_object* v_key_1260_; lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1273_; 
v_key_1260_ = lean_ctor_get(v_v_1251_, 0);
v_val_1261_ = lean_ctor_get(v_v_1251_, 1);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_v_1251_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1263_ = v_v_1251_;
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_inc(v_key_1260_);
lean_dec(v_v_1251_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
size_t v___x_1265_; size_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = lean_ptr_addr(v_x_1240_);
v___x_1266_ = lean_ptr_addr(v_key_1260_);
v___x_1267_ = lean_usize_dec_eq(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_del_object(v___x_1263_);
v___x_1268_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1260_, v_val_1261_, v_x_1240_, v_x_1241_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
v___y_1255_ = v___x_1269_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1271_; 
lean_dec(v_val_1261_);
lean_dec(v_key_1260_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_x_1241_);
lean_ctor_set(v___x_1263_, 0, v_x_1240_);
v___x_1271_ = v___x_1263_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_x_1240_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_x_1241_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v___y_1255_ = v___x_1271_;
goto v___jp_1254_;
}
}
}
}
case 1:
{
lean_object* v_node_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1286_; 
v_node_1274_ = lean_ctor_get(v_v_1251_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_v_1251_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1276_ = v_v_1251_;
v_isShared_1277_ = v_isSharedCheck_1286_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_node_1274_);
lean_dec(v_v_1251_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1286_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1278_ = ((size_t)5ULL);
v___x_1279_ = lean_usize_shift_right(v_x_1238_, v___x_1278_);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_x_1239_, v___x_1280_);
v___x_1282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_1274_, v___x_1279_, v___x_1281_, v_x_1240_, v_x_1241_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1282_);
v___x_1284_ = v___x_1276_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
v___y_1255_ = v___x_1284_;
goto v___jp_1254_;
}
}
}
default: 
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_x_1240_);
lean_ctor_set(v___x_1287_, 1, v_x_1241_);
v___y_1255_ = v___x_1287_;
goto v___jp_1254_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_array_fset(v_xs_x27_1253_, v_j_1245_, v___y_1255_);
lean_dec(v_j_1245_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1256_);
v___x_1258_ = v___x_1249_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_ks_1290_; lean_object* v_vs_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1311_; 
v_ks_1290_ = lean_ctor_get(v_x_1237_, 0);
v_vs_1291_ = lean_ctor_get(v_x_1237_, 1);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1293_ = v_x_1237_;
v_isShared_1294_ = v_isSharedCheck_1311_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_vs_1291_);
lean_inc(v_ks_1290_);
lean_dec(v_x_1237_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1311_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_ks_1290_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_vs_1291_);
v___x_1296_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v_newNode_1297_; uint8_t v___y_1299_; size_t v___x_1305_; uint8_t v___x_1306_; 
v_newNode_1297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_1296_, v_x_1240_, v_x_1241_);
v___x_1305_ = ((size_t)7ULL);
v___x_1306_ = lean_usize_dec_le(v___x_1305_, v_x_1239_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1297_);
v___x_1308_ = lean_unsigned_to_nat(4u);
v___x_1309_ = lean_nat_dec_lt(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
v___y_1299_ = v___x_1309_;
goto v___jp_1298_;
}
else
{
v___y_1299_ = v___x_1306_;
goto v___jp_1298_;
}
v___jp_1298_:
{
if (v___y_1299_ == 0)
{
lean_object* v_ks_1300_; lean_object* v_vs_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_ks_1300_ = lean_ctor_get(v_newNode_1297_, 0);
lean_inc_ref(v_ks_1300_);
v_vs_1301_ = lean_ctor_get(v_newNode_1297_, 1);
lean_inc_ref(v_vs_1301_);
lean_dec_ref(v_newNode_1297_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
v___x_1304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_1239_, v_ks_1300_, v_vs_1301_, v___x_1302_, v___x_1303_);
lean_dec_ref(v_vs_1301_);
lean_dec_ref(v_ks_1300_);
return v___x_1304_;
}
else
{
return v_newNode_1297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1312_, lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_i_1315_, lean_object* v_entries_1316_){
_start:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_get_size(v_keys_1313_);
v___x_1318_ = lean_nat_dec_lt(v_i_1315_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec(v_i_1315_);
return v_entries_1316_;
}
else
{
lean_object* v_k_1319_; lean_object* v_v_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; uint64_t v___x_1324_; size_t v_h_1325_; size_t v___x_1326_; lean_object* v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; size_t v_h_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_k_1319_ = lean_array_fget_borrowed(v_keys_1313_, v_i_1315_);
v_v_1320_ = lean_array_fget_borrowed(v_vals_1314_, v_i_1315_);
v___x_1321_ = lean_ptr_addr(v_k_1319_);
v___x_1322_ = ((size_t)3ULL);
v___x_1323_ = lean_usize_shift_right(v___x_1321_, v___x_1322_);
v___x_1324_ = lean_usize_to_uint64(v___x_1323_);
v_h_1325_ = lean_uint64_to_usize(v___x_1324_);
v___x_1326_ = ((size_t)5ULL);
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v_depth_1312_, v___x_1328_);
v___x_1330_ = lean_usize_mul(v___x_1326_, v___x_1329_);
v_h_1331_ = lean_usize_shift_right(v_h_1325_, v___x_1330_);
v___x_1332_ = lean_nat_add(v_i_1315_, v___x_1327_);
lean_dec(v_i_1315_);
lean_inc(v_v_1320_);
lean_inc(v_k_1319_);
v___x_1333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_1316_, v_h_1331_, v_depth_1312_, v_k_1319_, v_v_1320_);
v_i_1315_ = v___x_1332_;
v_entries_1316_ = v___x_1333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1335_, lean_object* v_keys_1336_, lean_object* v_vals_1337_, lean_object* v_i_1338_, lean_object* v_entries_1339_){
_start:
{
size_t v_depth_boxed_1340_; lean_object* v_res_1341_; 
v_depth_boxed_1340_ = lean_unbox_usize(v_depth_1335_);
lean_dec(v_depth_1335_);
v_res_1341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1340_, v_keys_1336_, v_vals_1337_, v_i_1338_, v_entries_1339_);
lean_dec_ref(v_vals_1337_);
lean_dec_ref(v_keys_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_){
_start:
{
size_t v_x_423__boxed_1347_; size_t v_x_424__boxed_1348_; lean_object* v_res_1349_; 
v_x_423__boxed_1347_ = lean_unbox_usize(v_x_1343_);
lean_dec(v_x_1343_);
v_x_424__boxed_1348_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_res_1349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1342_, v_x_423__boxed_1347_, v_x_424__boxed_1348_, v_x_1345_, v_x_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
size_t v___x_1353_; size_t v___x_1354_; size_t v___x_1355_; uint64_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1353_ = lean_ptr_addr(v_x_1351_);
v___x_1354_ = ((size_t)3ULL);
v___x_1355_ = lean_usize_shift_right(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_usize_to_uint64(v___x_1355_);
v___x_1357_ = lean_uint64_to_usize(v___x_1356_);
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1350_, v___x_1357_, v___x_1358_, v_x_1351_, v_x_1352_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* v_m_1360_, lean_object* v_e_1361_, lean_object* v_opId_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_m_1360_, v_e_1361_);
if (lean_obj_tag(v___x_1363_) == 1)
{
lean_object* v_val_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1362_, v_val_1364_);
v___x_1366_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1360_, v_e_1361_, v___x_1365_);
return v___x_1366_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v___x_1363_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_opId_1362_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1360_, v_e_1361_, v___x_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* v_00_u03b2_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_1371_, v_x_1372_, v_x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* v_00_u03b2_1375_, lean_object* v_x_1376_, size_t v_x_1377_, size_t v_x_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1376_, v_x_1377_, v_x_1378_, v_x_1379_, v_x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
size_t v_x_628__boxed_1388_; size_t v_x_629__boxed_1389_; lean_object* v_res_1390_; 
v_x_628__boxed_1388_ = lean_unbox_usize(v_x_1384_);
lean_dec(v_x_1384_);
v_x_629__boxed_1389_ = lean_unbox_usize(v_x_1385_);
lean_dec(v_x_1385_);
v_res_1390_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_1382_, v_x_1383_, v_x_628__boxed_1388_, v_x_629__boxed_1389_, v_x_1386_, v_x_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1391_, lean_object* v_n_1392_, lean_object* v_k_1393_, lean_object* v_v_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_1392_, v_k_1393_, v_v_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1396_, size_t v_depth_1397_, lean_object* v_keys_1398_, lean_object* v_vals_1399_, lean_object* v_heq_1400_, lean_object* v_i_1401_, lean_object* v_entries_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1397_, v_keys_1398_, v_vals_1399_, v_i_1401_, v_entries_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1404_, lean_object* v_depth_1405_, lean_object* v_keys_1406_, lean_object* v_vals_1407_, lean_object* v_heq_1408_, lean_object* v_i_1409_, lean_object* v_entries_1410_){
_start:
{
size_t v_depth_boxed_1411_; lean_object* v_res_1412_; 
v_depth_boxed_1411_ = lean_unbox_usize(v_depth_1405_);
lean_dec(v_depth_1405_);
v_res_1412_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_1404_, v_depth_boxed_1411_, v_keys_1406_, v_vals_1407_, v_heq_1408_, v_i_1409_, v_entries_1410_);
lean_dec_ref(v_vals_1407_);
lean_dec_ref(v_keys_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1414_, v_x_1415_, v_x_1416_, v_x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* v_e_1419_, lean_object* v_a_1420_, lean_object* v_s_1421_){
_start:
{
lean_object* v_structs_1422_; lean_object* v_opIdOf_1423_; lean_object* v_exprToOpIds_1424_; lean_object* v_steps_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_structs_1422_ = lean_ctor_get(v_s_1421_, 0);
v_opIdOf_1423_ = lean_ctor_get(v_s_1421_, 1);
v_exprToOpIds_1424_ = lean_ctor_get(v_s_1421_, 2);
v_steps_1425_ = lean_ctor_get(v_s_1421_, 3);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_s_1421_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v_s_1421_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_steps_1425_);
lean_inc(v_exprToOpIds_1424_);
lean_inc(v_opIdOf_1423_);
lean_inc(v_structs_1422_);
lean_dec(v_s_1421_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_inc(v_a_1420_);
v___x_1429_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(v_exprToOpIds_1424_, v_e_1419_, v_a_1420_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 2, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_structs_1422_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_opIdOf_1423_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_steps_1425_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object* v_e_1434_, lean_object* v_a_1435_, lean_object* v_s_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_1434_, v_a_1435_, v_s_1436_);
lean_dec(v_a_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* v_e_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_inc(v_a_1439_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1442_, 0, v_e_1438_);
lean_closure_set(v___f_1442_, 1, v_a_1439_);
v___x_1443_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1444_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1443_, v___f_1442_, v_a_1440_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* v_e_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec(v_a_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1450_, v_a_1451_, v_a_1452_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* v_e_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec(v_a_1465_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* v_e_1478_, lean_object* v_size_1479_, lean_object* v_s_1480_){
_start:
{
lean_object* v_id_1481_; lean_object* v_type_1482_; lean_object* v_u_1483_; lean_object* v_op_1484_; lean_object* v_neutral_x3f_1485_; lean_object* v_assocInst_1486_; lean_object* v_idempotentInst_x3f_1487_; lean_object* v_commInst_x3f_1488_; lean_object* v_neutralInst_x3f_1489_; lean_object* v_nextId_1490_; lean_object* v_vars_1491_; lean_object* v_varMap_1492_; lean_object* v_denote_1493_; lean_object* v_denoteEntries_1494_; lean_object* v_queue_1495_; lean_object* v_basis_1496_; lean_object* v_diseqs_1497_; uint8_t v_recheck_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1507_; 
v_id_1481_ = lean_ctor_get(v_s_1480_, 0);
v_type_1482_ = lean_ctor_get(v_s_1480_, 1);
v_u_1483_ = lean_ctor_get(v_s_1480_, 2);
v_op_1484_ = lean_ctor_get(v_s_1480_, 3);
v_neutral_x3f_1485_ = lean_ctor_get(v_s_1480_, 4);
v_assocInst_1486_ = lean_ctor_get(v_s_1480_, 5);
v_idempotentInst_x3f_1487_ = lean_ctor_get(v_s_1480_, 6);
v_commInst_x3f_1488_ = lean_ctor_get(v_s_1480_, 7);
v_neutralInst_x3f_1489_ = lean_ctor_get(v_s_1480_, 8);
v_nextId_1490_ = lean_ctor_get(v_s_1480_, 9);
v_vars_1491_ = lean_ctor_get(v_s_1480_, 10);
v_varMap_1492_ = lean_ctor_get(v_s_1480_, 11);
v_denote_1493_ = lean_ctor_get(v_s_1480_, 12);
v_denoteEntries_1494_ = lean_ctor_get(v_s_1480_, 13);
v_queue_1495_ = lean_ctor_get(v_s_1480_, 14);
v_basis_1496_ = lean_ctor_get(v_s_1480_, 15);
v_diseqs_1497_ = lean_ctor_get(v_s_1480_, 16);
v_recheck_1498_ = lean_ctor_get_uint8(v_s_1480_, sizeof(void*)*17);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_s_1480_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1500_ = v_s_1480_;
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_diseqs_1497_);
lean_inc(v_basis_1496_);
lean_inc(v_queue_1495_);
lean_inc(v_denoteEntries_1494_);
lean_inc(v_denote_1493_);
lean_inc(v_varMap_1492_);
lean_inc(v_vars_1491_);
lean_inc(v_nextId_1490_);
lean_inc(v_neutralInst_x3f_1489_);
lean_inc(v_commInst_x3f_1488_);
lean_inc(v_idempotentInst_x3f_1487_);
lean_inc(v_assocInst_1486_);
lean_inc(v_neutral_x3f_1485_);
lean_inc(v_op_1484_);
lean_inc(v_u_1483_);
lean_inc(v_type_1482_);
lean_inc(v_id_1481_);
lean_dec(v_s_1480_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_inc_ref(v_e_1478_);
v___x_1502_ = l_Lean_PersistentArray_push___redArg(v_vars_1491_, v_e_1478_);
v___x_1503_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_1492_, v_e_1478_, v_size_1479_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 11, v___x_1503_);
lean_ctor_set(v___x_1500_, 10, v___x_1502_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_id_1481_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_type_1482_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_u_1483_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_op_1484_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_neutral_x3f_1485_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v_assocInst_1486_);
lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_idempotentInst_x3f_1487_);
lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_commInst_x3f_1488_);
lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_neutralInst_x3f_1489_);
lean_ctor_set(v_reuseFailAlloc_1506_, 9, v_nextId_1490_);
lean_ctor_set(v_reuseFailAlloc_1506_, 10, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1506_, 11, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 12, v_denote_1493_);
lean_ctor_set(v_reuseFailAlloc_1506_, 13, v_denoteEntries_1494_);
lean_ctor_set(v_reuseFailAlloc_1506_, 14, v_queue_1495_);
lean_ctor_set(v_reuseFailAlloc_1506_, 15, v_basis_1496_);
lean_ctor_set(v_reuseFailAlloc_1506_, 16, v_diseqs_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*17, v_recheck_1498_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* v_e_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1571_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1571_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1571_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_vars_1526_; lean_object* v_varMap_1527_; lean_object* v___x_1528_; 
v_vars_1526_ = lean_ctor_get(v_a_1522_, 10);
lean_inc_ref(v_vars_1526_);
v_varMap_1527_ = lean_ctor_get(v_a_1522_, 11);
lean_inc_ref(v_varMap_1527_);
lean_dec(v_a_1522_);
v___x_1528_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_1527_, v_e_1508_);
lean_dec_ref(v_varMap_1527_);
if (lean_obj_tag(v___x_1528_) == 1)
{
lean_object* v_val_1529_; lean_object* v___x_1531_; 
lean_dec_ref(v_vars_1526_);
lean_dec_ref(v_e_1508_);
v_val_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1529_);
lean_dec_ref_known(v___x_1528_, 1);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v_val_1529_);
v___x_1531_ = v___x_1524_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_val_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v_size_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; 
lean_dec(v___x_1528_);
lean_del_object(v___x_1524_);
v_size_1533_ = lean_ctor_get(v_vars_1526_, 2);
lean_inc_n(v_size_1533_, 2);
lean_dec_ref(v_vars_1526_);
lean_inc_ref(v_e_1508_);
v___f_1534_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(v___f_1534_, 0, v_e_1508_);
lean_closure_set(v___f_1534_, 1, v_size_1533_);
v___x_1535_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_1534_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref_known(v___x_1535_, 1);
lean_inc_ref(v_e_1508_);
v___x_1536_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1508_, v_a_1509_, v_a_1510_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref_known(v___x_1536_, 1);
v___x_1537_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1538_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1537_, v_e_1508_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_size_1533_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_size_1533_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_size_1533_);
v_a_1547_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1538_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1538_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_size_1533_);
lean_dec_ref(v_e_1508_);
v_a_1555_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1536_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1536_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_size_1533_);
lean_dec_ref(v_e_1508_);
v_a_1563_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1535_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1535_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v_e_1508_);
v_a_1572_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1521_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1521_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* v_e_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec(v_a_1581_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* v_e_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v_mctx_1598_; lean_object* v___x_1599_; lean_object* v_fst_1600_; lean_object* v_snd_1601_; lean_object* v___x_1602_; lean_object* v_cache_1603_; lean_object* v_zetaDeltaFVarIds_1604_; lean_object* v_postponed_1605_; lean_object* v_diag_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1615_; 
v___x_1597_ = lean_st_ref_get(v___y_1595_);
v_mctx_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc_ref(v_mctx_1598_);
lean_dec(v___x_1597_);
v___x_1599_ = lean_instantiate_expr_mvars(v_mctx_1598_, v_e_1594_);
v_fst_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_fst_1600_);
v_snd_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_snd_1601_);
lean_dec_ref(v___x_1599_);
v___x_1602_ = lean_st_ref_take(v___y_1595_);
v_cache_1603_ = lean_ctor_get(v___x_1602_, 1);
v_zetaDeltaFVarIds_1604_ = lean_ctor_get(v___x_1602_, 2);
v_postponed_1605_ = lean_ctor_get(v___x_1602_, 3);
v_diag_1606_ = lean_ctor_get(v___x_1602_, 4);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v___x_1602_, 0);
lean_dec(v_unused_1616_);
v___x_1608_ = v___x_1602_;
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_diag_1606_);
lean_inc(v_postponed_1605_);
lean_inc(v_zetaDeltaFVarIds_1604_);
lean_inc(v_cache_1603_);
lean_dec(v___x_1602_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v_fst_1600_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_fst_1600_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_cache_1603_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_zetaDeltaFVarIds_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_postponed_1605_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_diag_1606_);
v___x_1611_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_st_ref_put(v___y_1595_, v___x_1611_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_snd_1601_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* v_e_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1617_, v___y_1618_);
lean_dec(v___y_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* v_e_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1621_, v___y_1629_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* v_e_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec(v___y_1635_);
return v_res_1646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_unsigned_to_nat(32u);
v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1(void){
_start:
{
size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1650_ = ((size_t)5ULL);
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_unsigned_to_nat(32u);
v___x_1653_ = lean_mk_empty_array_with_capacity(v___x_1652_);
v___x_1654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
v___x_1655_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
lean_ctor_set(v___x_1655_, 2, v___x_1651_);
lean_ctor_set(v___x_1655_, 3, v___x_1651_);
lean_ctor_set_usize(v___x_1655_, 4, v___x_1650_);
return v___x_1655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* v___x_1659_, lean_object* v_binderType_1660_, lean_object* v_a_1661_, lean_object* v_op_1662_, lean_object* v_snd_1663_, lean_object* v_val_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_fst_1667_, uint8_t v_a_1668_, lean_object* v_s_1669_){
_start:
{
lean_object* v_structs_1670_; lean_object* v_opIdOf_1671_; lean_object* v_exprToOpIds_1672_; lean_object* v_steps_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1687_; 
v_structs_1670_ = lean_ctor_get(v_s_1669_, 0);
v_opIdOf_1671_ = lean_ctor_get(v_s_1669_, 1);
v_exprToOpIds_1672_ = lean_ctor_get(v_s_1669_, 2);
v_steps_1673_ = lean_ctor_get(v_s_1669_, 3);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_s_1669_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1675_ = v_s_1669_;
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_steps_1673_);
lean_inc(v_exprToOpIds_1672_);
lean_inc(v_opIdOf_1671_);
lean_inc(v_structs_1670_);
lean_dec(v_s_1669_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
v___x_1680_ = lean_box(1);
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_1682_, 0, v___x_1659_);
lean_ctor_set(v___x_1682_, 1, v_binderType_1660_);
lean_ctor_set(v___x_1682_, 2, v_a_1661_);
lean_ctor_set(v___x_1682_, 3, v_op_1662_);
lean_ctor_set(v___x_1682_, 4, v_snd_1663_);
lean_ctor_set(v___x_1682_, 5, v_val_1664_);
lean_ctor_set(v___x_1682_, 6, v_a_1665_);
lean_ctor_set(v___x_1682_, 7, v_a_1666_);
lean_ctor_set(v___x_1682_, 8, v_fst_1667_);
lean_ctor_set(v___x_1682_, 9, v___x_1677_);
lean_ctor_set(v___x_1682_, 10, v___x_1678_);
lean_ctor_set(v___x_1682_, 11, v___x_1679_);
lean_ctor_set(v___x_1682_, 12, v___x_1679_);
lean_ctor_set(v___x_1682_, 13, v___x_1678_);
lean_ctor_set(v___x_1682_, 14, v___x_1680_);
lean_ctor_set(v___x_1682_, 15, v___x_1681_);
lean_ctor_set(v___x_1682_, 16, v___x_1678_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*17, v_a_1668_);
v___x_1683_ = lean_array_push(v_structs_1670_, v___x_1682_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1683_);
v___x_1685_ = v___x_1675_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_opIdOf_1671_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_exprToOpIds_1672_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_steps_1673_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* v___x_1688_, lean_object* v_binderType_1689_, lean_object* v_a_1690_, lean_object* v_op_1691_, lean_object* v_snd_1692_, lean_object* v_val_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_fst_1696_, lean_object* v_a_1697_, lean_object* v_s_1698_){
_start:
{
uint8_t v_a_174805__boxed_1699_; lean_object* v_res_1700_; 
v_a_174805__boxed_1699_ = lean_unbox(v_a_1697_);
v_res_1700_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1688_, v_binderType_1689_, v_a_1690_, v_op_1691_, v_snd_1692_, v_val_1693_, v_a_1694_, v_a_1695_, v_fst_1696_, v_a_174805__boxed_1699_, v_s_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg(lean_object* v_m_1701_, lean_object* v_query_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_1701_, v_query_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_index_1704_; lean_object* v_key_1705_; lean_object* v_value_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_index_1704_ = lean_ctor_get(v___x_1703_, 0);
v_key_1705_ = lean_ctor_get(v___x_1703_, 1);
v_value_1706_ = lean_ctor_get(v___x_1703_, 2);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1703_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_value_1706_);
lean_inc(v_key_1705_);
lean_inc(v_index_1704_);
lean_dec(v___x_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_index_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_key_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_value_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v___x_1714_; 
lean_dec(v___x_1703_);
v___x_1714_ = lean_box(1);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg___boxed(lean_object* v_m_1715_, lean_object* v_query_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg(v_m_1715_, v_query_1716_);
lean_dec(v_query_1716_);
lean_dec_ref(v_m_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* v_m_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg(v_m_1718_, v_a_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
uint8_t v___x_1721_; 
lean_dec_ref_known(v___x_1720_, 3);
v___x_1721_ = 1;
return v___x_1721_;
}
else
{
uint8_t v___x_1722_; 
v___x_1722_ = 0;
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* v_m_1723_, lean_object* v_a_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_m_1723_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1727_; double v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_float_of_nat(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* v_cls_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_ref_1739_; lean_object* v___x_1740_; lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1785_; 
v_ref_1739_ = lean_ctor_get(v___y_1736_, 5);
v___x_1740_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1785_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1785_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v_traceState_1746_; lean_object* v_env_1747_; lean_object* v_nextMacroScope_1748_; lean_object* v_ngen_1749_; lean_object* v_auxDeclNGen_1750_; lean_object* v_cache_1751_; lean_object* v_messages_1752_; lean_object* v_infoState_1753_; lean_object* v_snapshotTasks_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1784_; 
v___x_1745_ = lean_st_ref_take(v___y_1737_);
v_traceState_1746_ = lean_ctor_get(v___x_1745_, 4);
v_env_1747_ = lean_ctor_get(v___x_1745_, 0);
v_nextMacroScope_1748_ = lean_ctor_get(v___x_1745_, 1);
v_ngen_1749_ = lean_ctor_get(v___x_1745_, 2);
v_auxDeclNGen_1750_ = lean_ctor_get(v___x_1745_, 3);
v_cache_1751_ = lean_ctor_get(v___x_1745_, 5);
v_messages_1752_ = lean_ctor_get(v___x_1745_, 6);
v_infoState_1753_ = lean_ctor_get(v___x_1745_, 7);
v_snapshotTasks_1754_ = lean_ctor_get(v___x_1745_, 8);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1756_ = v___x_1745_;
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snapshotTasks_1754_);
lean_inc(v_infoState_1753_);
lean_inc(v_messages_1752_);
lean_inc(v_cache_1751_);
lean_inc(v_traceState_1746_);
lean_inc(v_auxDeclNGen_1750_);
lean_inc(v_ngen_1749_);
lean_inc(v_nextMacroScope_1748_);
lean_inc(v_env_1747_);
lean_dec(v___x_1745_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
uint64_t v_tid_1758_; lean_object* v_traces_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1783_; 
v_tid_1758_ = lean_ctor_get_uint64(v_traceState_1746_, sizeof(void*)*1);
v_traces_1759_ = lean_ctor_get(v_traceState_1746_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_traceState_1746_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1761_ = v_traceState_1746_;
v_isShared_1762_ = v_isSharedCheck_1783_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_traces_1759_);
lean_dec(v_traceState_1746_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1783_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; double v___x_1764_; uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
v___x_1765_ = 0;
v___x_1766_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
v___x_1767_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1767_, 0, v_cls_1732_);
lean_ctor_set(v___x_1767_, 1, v___x_1763_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
lean_ctor_set_float(v___x_1767_, sizeof(void*)*3, v___x_1764_);
lean_ctor_set_float(v___x_1767_, sizeof(void*)*3 + 8, v___x_1764_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*3 + 16, v___x_1765_);
v___x_1768_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2));
v___x_1769_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v_a_1741_);
lean_ctor_set(v___x_1769_, 2, v___x_1768_);
lean_inc(v_ref_1739_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_ref_1739_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_PersistentArray_push___redArg(v_traces_1759_, v___x_1770_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1771_);
v___x_1773_ = v___x_1761_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1771_);
lean_ctor_set_uint64(v_reuseFailAlloc_1782_, sizeof(void*)*1, v_tid_1758_);
v___x_1773_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 4, v___x_1773_);
v___x_1775_ = v___x_1756_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_env_1747_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_nextMacroScope_1748_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_ngen_1749_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_auxDeclNGen_1750_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1781_, 5, v_cache_1751_);
lean_ctor_set(v_reuseFailAlloc_1781_, 6, v_messages_1752_);
lean_ctor_set(v_reuseFailAlloc_1781_, 7, v_infoState_1753_);
lean_ctor_set(v_reuseFailAlloc_1781_, 8, v_snapshotTasks_1754_);
v___x_1775_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1776_ = lean_st_ref_put(v___y_1737_, v___x_1775_);
v___x_1777_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1777_);
v___x_1779_ = v___x_1743_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* v_cls_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1786_, v_msg_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
v___x_1801_ = l_Lean_MessageData_ofFormat(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15));
v___x_1821_ = l_Lean_Name_append(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__29));
v___x_1847_ = l_Lean_mkConst(v___x_1846_, v___x_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* v_op_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___y_1861_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v_neutral_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v_f_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; 
v_f_2069_ = l_Lean_Expr_getAppFn(v_op_1848_);
if (lean_obj_tag(v_f_2069_) == 4)
{
lean_object* v_declName_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_declName_2322_ = lean_ctor_get(v_f_2069_, 0);
lean_inc(v_declName_2322_);
v___x_2323_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_2323_, v_declName_2322_);
lean_dec(v_declName_2322_);
if (v___x_2324_ == 0)
{
v___y_2071_ = v_a_1849_;
v___y_2072_ = v_a_1850_;
v___y_2073_ = v_a_1851_;
v___y_2074_ = v_a_1852_;
v___y_2075_ = v_a_1853_;
v___y_2076_ = v_a_1854_;
v___y_2077_ = v_a_1855_;
v___y_2078_ = v_a_1856_;
v___y_2079_ = v_a_1857_;
v___y_2080_ = v_a_1858_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref_known(v_f_2069_, 2);
lean_dec_ref(v_op_1848_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
else
{
v___y_2071_ = v_a_1849_;
v___y_2072_ = v_a_1850_;
v___y_2073_ = v_a_1851_;
v___y_2074_ = v_a_1852_;
v___y_2075_ = v_a_1853_;
v___y_2076_ = v_a_1854_;
v___y_2077_ = v_a_1855_;
v___y_2078_ = v_a_1856_;
v___y_2079_ = v_a_1857_;
v___y_2080_ = v_a_1858_;
goto v___jp_2070_;
}
v___jp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1861_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
v___jp_1864_:
{
if (lean_obj_tag(v___y_1865_) == 1)
{
lean_object* v_val_1877_; lean_object* v___x_1878_; 
v_val_1877_ = lean_ctor_get(v___y_1865_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___y_1865_, 1);
v___x_1878_ = l_Lean_Meta_Grind_AC_mkVar(v_val_1877_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_dec_ref_known(v___x_1878_, 1);
v___y_1861_ = v___y_1866_;
goto v___jp_1860_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v___y_1866_);
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_dec(v___y_1865_);
v___y_1861_ = v___y_1866_;
goto v___jp_1860_;
}
}
v___jp_1887_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1897_);
lean_ctor_set(v___x_1903_, 1, v___y_1902_);
lean_inc(v___y_1888_);
v___x_1904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_1888_, v___x_1903_, v___y_1894_, v___y_1892_, v___y_1891_, v___y_1893_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_dec_ref_known(v___x_1904_, 1);
v___y_1865_ = v___y_1899_;
v___y_1866_ = v___y_1901_;
v___y_1867_ = v___y_1900_;
v___y_1868_ = v___y_1895_;
v___y_1869_ = v___y_1890_;
v___y_1870_ = v___y_1898_;
v___y_1871_ = v___y_1889_;
v___y_1872_ = v___y_1896_;
v___y_1873_ = v___y_1894_;
v___y_1874_ = v___y_1892_;
v___y_1875_ = v___y_1891_;
v___y_1876_ = v___y_1893_;
goto v___jp_1864_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v___y_1901_);
lean_dec(v___y_1899_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
v___jp_1913_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_inc_ref(v___y_1928_);
v___x_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___y_1928_);
v___x_1930_ = l_Lean_MessageData_ofFormat(v___x_1929_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___y_1920_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
if (lean_obj_tag(v___y_1925_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
v___y_1888_ = v___y_1914_;
v___y_1889_ = v___y_1915_;
v___y_1890_ = v___y_1916_;
v___y_1891_ = v___y_1917_;
v___y_1892_ = v___y_1918_;
v___y_1893_ = v___y_1919_;
v___y_1894_ = v___y_1921_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___x_1933_;
v___y_1898_ = v___y_1924_;
v___y_1899_ = v___y_1925_;
v___y_1900_ = v___y_1926_;
v___y_1901_ = v___y_1927_;
v___y_1902_ = v___x_1934_;
goto v___jp_1887_;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1936_; 
v_val_1935_ = lean_ctor_get(v___y_1925_, 0);
lean_inc(v_val_1935_);
v___x_1936_ = l_Lean_MessageData_ofExpr(v_val_1935_);
v___y_1888_ = v___y_1914_;
v___y_1889_ = v___y_1915_;
v___y_1890_ = v___y_1916_;
v___y_1891_ = v___y_1917_;
v___y_1892_ = v___y_1918_;
v___y_1893_ = v___y_1919_;
v___y_1894_ = v___y_1921_;
v___y_1895_ = v___y_1922_;
v___y_1896_ = v___y_1923_;
v___y_1897_ = v___x_1933_;
v___y_1898_ = v___y_1924_;
v___y_1899_ = v___y_1925_;
v___y_1900_ = v___y_1926_;
v___y_1901_ = v___y_1927_;
v___y_1902_ = v___x_1936_;
goto v___jp_1887_;
}
}
v___jp_1937_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_inc_ref(v___y_1953_);
v___x_1954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1953_);
v___x_1955_ = l_Lean_MessageData_ofFormat(v___x_1954_);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___y_1945_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
if (lean_obj_tag(v___y_1946_) == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1914_ = v___y_1938_;
v___y_1915_ = v___y_1939_;
v___y_1916_ = v___y_1940_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1942_;
v___y_1919_ = v___y_1943_;
v___y_1920_ = v___x_1958_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v___y_1947_;
v___y_1923_ = v___y_1948_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1950_;
v___y_1926_ = v___y_1951_;
v___y_1927_ = v___y_1952_;
v___y_1928_ = v___x_1959_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1960_; 
lean_dec_ref_known(v___y_1946_, 1);
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1914_ = v___y_1938_;
v___y_1915_ = v___y_1939_;
v___y_1916_ = v___y_1940_;
v___y_1917_ = v___y_1941_;
v___y_1918_ = v___y_1942_;
v___y_1919_ = v___y_1943_;
v___y_1920_ = v___x_1958_;
v___y_1921_ = v___y_1944_;
v___y_1922_ = v___y_1947_;
v___y_1923_ = v___y_1948_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v___y_1950_;
v___y_1926_ = v___y_1951_;
v___y_1927_ = v___y_1952_;
v___y_1928_ = v___x_1960_;
goto v___jp_1913_;
}
}
v___jp_1961_:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_1972_, v___y_1980_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v_structs_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v_structs_1984_ = lean_ctor_get(v_a_1983_, 0);
lean_inc_ref(v_structs_1984_);
lean_dec(v_a_1983_);
v___x_1985_ = lean_array_get_size(v_structs_1984_);
lean_dec_ref(v_structs_1984_);
v___x_1986_ = lean_box(v___y_1967_);
lean_inc(v_snd_1971_);
lean_inc_ref(v_op_1848_);
v___f_1987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(v___f_1987_, 0, v___x_1985_);
lean_closure_set(v___f_1987_, 1, v___y_1965_);
lean_closure_set(v___f_1987_, 2, v___y_1962_);
lean_closure_set(v___f_1987_, 3, v_op_1848_);
lean_closure_set(v___f_1987_, 4, v_snd_1971_);
lean_closure_set(v___f_1987_, 5, v___y_1963_);
lean_closure_set(v___f_1987_, 6, v___y_1964_);
lean_closure_set(v___f_1987_, 7, v___y_1966_);
lean_closure_set(v___f_1987_, 8, v_fst_1970_);
lean_closure_set(v___f_1987_, 9, v___x_1986_);
v___x_1988_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1989_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1988_, v___f_1987_, v___y_1972_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_options_1990_; uint8_t v_hasTrace_1991_; 
lean_dec_ref_known(v___x_1989_, 1);
v_options_1990_ = lean_ctor_get(v___y_1980_, 2);
v_hasTrace_1991_ = lean_ctor_get_uint8(v_options_1990_, sizeof(void*)*1);
if (v_hasTrace_1991_ == 0)
{
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v_op_1848_);
v___y_1865_ = v_snd_1971_;
v___y_1866_ = v___x_1985_;
v___y_1867_ = v___y_1972_;
v___y_1868_ = v___y_1973_;
v___y_1869_ = v___y_1974_;
v___y_1870_ = v___y_1975_;
v___y_1871_ = v___y_1976_;
v___y_1872_ = v___y_1977_;
v___y_1873_ = v___y_1978_;
v___y_1874_ = v___y_1979_;
v___y_1875_ = v___y_1980_;
v___y_1876_ = v___y_1981_;
goto v___jp_1864_;
}
else
{
lean_object* v_inheritedTraceOptions_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_inheritedTraceOptions_1992_ = lean_ctor_get(v___y_1980_, 13);
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
v___x_1995_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1992_, v_options_1990_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v_op_1848_);
v___y_1865_ = v_snd_1971_;
v___y_1866_ = v___x_1985_;
v___y_1867_ = v___y_1972_;
v___y_1868_ = v___y_1973_;
v___y_1869_ = v___y_1974_;
v___y_1870_ = v___y_1975_;
v___y_1871_ = v___y_1976_;
v___y_1872_ = v___y_1977_;
v___y_1873_ = v___y_1978_;
v___y_1874_ = v___y_1979_;
v___y_1875_ = v___y_1980_;
v___y_1876_ = v___y_1981_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = l_Lean_MessageData_ofExpr(v_op_1848_);
v___x_1997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
if (lean_obj_tag(v___y_1969_) == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1938_ = v___x_1993_;
v___y_1939_ = v___y_1976_;
v___y_1940_ = v___y_1974_;
v___y_1941_ = v___y_1980_;
v___y_1942_ = v___y_1979_;
v___y_1943_ = v___y_1981_;
v___y_1944_ = v___y_1978_;
v___y_1945_ = v___x_1998_;
v___y_1946_ = v___y_1968_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1977_;
v___y_1949_ = v___y_1975_;
v___y_1950_ = v_snd_1971_;
v___y_1951_ = v___y_1972_;
v___y_1952_ = v___x_1985_;
v___y_1953_ = v___x_1999_;
goto v___jp_1937_;
}
else
{
lean_object* v___x_2000_; 
lean_dec_ref_known(v___y_1969_, 1);
v___x_2000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1938_ = v___x_1993_;
v___y_1939_ = v___y_1976_;
v___y_1940_ = v___y_1974_;
v___y_1941_ = v___y_1980_;
v___y_1942_ = v___y_1979_;
v___y_1943_ = v___y_1981_;
v___y_1944_ = v___y_1978_;
v___y_1945_ = v___x_1998_;
v___y_1946_ = v___y_1968_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1977_;
v___y_1949_ = v___y_1975_;
v___y_1950_ = v_snd_1971_;
v___y_1951_ = v___y_1972_;
v___y_1952_ = v___x_1985_;
v___y_1953_ = v___x_2000_;
goto v___jp_1937_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_snd_1971_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v_op_1848_);
v_a_2001_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1989_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_snd_1971_);
lean_dec(v_fst_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v_op_1848_);
v_a_2009_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1982_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1982_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
v___jp_2017_:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_neutral_2027_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_1848_, v___y_2028_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = lean_box(0);
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
lean_inc(v___y_2029_);
lean_inc(v___y_2028_);
lean_inc(v_a_2039_);
v___x_2043_ = lean_grind_internalize(v_a_2039_, v_a_2041_, v___x_2042_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2044_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_a_2039_);
v___y_1962_ = v___y_2018_;
v___y_1963_ = v___y_2019_;
v___y_1964_ = v___y_2020_;
v___y_1965_ = v___y_2021_;
v___y_1966_ = v___y_2022_;
v___y_1967_ = v___y_2023_;
v___y_1968_ = v___y_2024_;
v___y_1969_ = v___y_2026_;
v_fst_1970_ = v___y_2025_;
v_snd_1971_ = v___x_2044_;
v___y_1972_ = v___y_2028_;
v___y_1973_ = v___y_2029_;
v___y_1974_ = v___y_2030_;
v___y_1975_ = v___y_2031_;
v___y_1976_ = v___y_2032_;
v___y_1977_ = v___y_2033_;
v___y_1978_ = v___y_2034_;
v___y_1979_ = v___y_2035_;
v___y_1980_ = v___y_2036_;
v___y_1981_ = v___y_2037_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2039_);
lean_dec(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v_op_1848_);
v_a_2045_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2043_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2039_);
lean_dec(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v_op_1848_);
v_a_2053_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2040_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2040_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v_op_1848_);
v_a_2061_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2038_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2038_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
v___jp_2070_:
{
lean_object* v___x_2081_; 
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc_ref(v_op_1848_);
v___x_2081_ = lean_infer_type(v_op_1848_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2083_ = lean_whnf(v_a_2082_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2305_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2305_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2305_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
if (lean_obj_tag(v_a_2084_) == 7)
{
lean_object* v_binderType_2088_; lean_object* v_body_2089_; uint8_t v___x_2090_; 
v_binderType_2088_ = lean_ctor_get(v_a_2084_, 1);
lean_inc_ref(v_binderType_2088_);
v_body_2089_ = lean_ctor_get(v_a_2084_, 2);
lean_inc_ref(v_body_2089_);
lean_dec_ref_known(v_a_2084_, 3);
v___x_2090_ = l_Lean_Expr_hasLooseBVars(v_body_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_del_object(v___x_2086_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
v___x_2091_ = lean_whnf(v_body_2089_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2288_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2288_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2288_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
if (lean_obj_tag(v_a_2092_) == 7)
{
lean_object* v_binderType_2096_; lean_object* v_body_2097_; uint8_t v___x_2098_; 
v_binderType_2096_ = lean_ctor_get(v_a_2092_, 1);
lean_inc_ref(v_binderType_2096_);
v_body_2097_ = lean_ctor_get(v_a_2092_, 2);
lean_inc_ref(v_body_2097_);
lean_dec_ref_known(v_a_2092_, 3);
v___x_2098_ = l_Lean_Expr_hasLooseBVars(v_body_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_del_object(v___x_2094_);
lean_inc_ref(v_binderType_2088_);
v___x_2099_ = l_Lean_Meta_isExprDefEq(v_binderType_2088_, v_binderType_2096_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2271_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2271_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2271_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_unbox(v_a_2100_);
lean_dec(v_a_2100_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec_ref(v_body_2097_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2105_ = lean_box(0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2105_);
v___x_2107_ = v___x_2102_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v___x_2109_; 
lean_del_object(v___x_2102_);
lean_inc_ref(v_binderType_2088_);
v___x_2109_ = l_Lean_Meta_isExprDefEq(v_binderType_2088_, v_body_2097_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2262_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2262_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2262_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_unbox(v_a_2110_);
lean_dec(v_a_2110_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2115_ = lean_box(0);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
else
{
lean_object* v___x_2119_; 
lean_del_object(v___x_2112_);
v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_1848_, v_f_2069_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec_ref(v_f_2069_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2253_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2253_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2253_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_unbox(v_a_2120_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_del_object(v___x_2122_);
lean_inc_ref(v_binderType_2088_);
v___x_2125_ = l_Lean_Meta_getLevel(v_binderType_2088_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_n(v_a_2126_, 2);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21));
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_a_2126_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
lean_inc_ref(v___x_2129_);
v___x_2130_ = l_Lean_mkConst(v___x_2127_, v___x_2129_);
lean_inc_ref(v_op_1848_);
lean_inc_ref(v_binderType_2088_);
v___x_2131_ = l_Lean_mkAppB(v___x_2130_, v_binderType_2088_, v_op_1848_);
v___x_2132_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2131_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2232_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2232_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2232_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
if (lean_obj_tag(v_a_2133_) == 1)
{
lean_object* v_val_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2135_);
v_val_2137_ = lean_ctor_get(v_a_2133_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2139_ = v_a_2133_;
v_isShared_2140_ = v_isSharedCheck_2227_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_val_2137_);
lean_dec(v_a_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2227_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23));
lean_inc_ref(v___x_2129_);
v___x_2142_ = l_Lean_mkConst(v___x_2141_, v___x_2129_);
lean_inc_ref(v_op_1848_);
lean_inc_ref(v_binderType_2088_);
v___x_2143_ = l_Lean_mkAppB(v___x_2142_, v_binderType_2088_, v_op_1848_);
v___x_2144_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2143_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25));
lean_inc_ref(v___x_2129_);
v___x_2147_ = l_Lean_mkConst(v___x_2146_, v___x_2129_);
lean_inc_ref(v_op_1848_);
lean_inc_ref(v_binderType_2088_);
v___x_2148_ = l_Lean_mkAppB(v___x_2147_, v_binderType_2088_, v_op_1848_);
v___x_2149_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2148_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
lean_inc_ref(v_binderType_2088_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_binderType_2088_);
v___x_2152_ = v___x_2139_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_binderType_2088_);
v___x_2152_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = 0;
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_Meta_mkFreshExprMVar(v___x_2152_, v___x_2153_, v___x_2154_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc_n(v_a_2156_, 2);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27));
v___x_2158_ = l_Lean_mkConst(v___x_2157_, v___x_2129_);
lean_inc_ref(v_op_1848_);
lean_inc_ref(v_binderType_2088_);
v___x_2159_ = l_Lean_mkApp3(v___x_2158_, v_binderType_2088_, v_op_1848_, v_a_2156_);
v___x_2160_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2159_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
if (lean_obj_tag(v_a_2161_) == 1)
{
lean_object* v___x_2162_; lean_object* v_a_2163_; lean_object* v___x_2164_; 
v___x_2162_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_2156_, v___y_2078_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_n(v_a_2163_, 2);
lean_dec_ref(v___x_2162_);
v___x_2164_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2163_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2166_; lean_object* v_fst_2167_; lean_object* v_snd_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_a_2163_);
v_val_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_a_2165_, 1);
v_fst_2167_ = lean_ctor_get(v_val_2166_, 0);
lean_inc(v_fst_2167_);
v_snd_2168_ = lean_ctor_get(v_val_2166_, 1);
lean_inc(v_snd_2168_);
lean_dec(v_val_2166_);
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30);
v___x_2170_ = l_Lean_mkNatLit(v_fst_2167_);
v___x_2171_ = l_Lean_Expr_app___override(v___x_2169_, v___x_2170_);
v___x_2172_ = l_Lean_Meta_mkNumeral(v___x_2171_, v_snd_2168_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_unbox(v_a_2120_);
lean_dec(v_a_2120_);
lean_inc(v_a_2145_);
lean_inc(v_a_2150_);
v___y_2018_ = v_a_2126_;
v___y_2019_ = v_val_2137_;
v___y_2020_ = v_a_2150_;
v___y_2021_ = v_binderType_2088_;
v___y_2022_ = v_a_2145_;
v___y_2023_ = v___x_2174_;
v___y_2024_ = v_a_2150_;
v___y_2025_ = v_a_2161_;
v___y_2026_ = v_a_2145_;
v_neutral_2027_ = v_a_2173_;
v___y_2028_ = v___y_2071_;
v___y_2029_ = v___y_2072_;
v___y_2030_ = v___y_2073_;
v___y_2031_ = v___y_2074_;
v___y_2032_ = v___y_2075_;
v___y_2033_ = v___y_2076_;
v___y_2034_ = v___y_2077_;
v___y_2035_ = v___y_2078_;
v___y_2036_ = v___y_2079_;
v___y_2037_ = v___y_2080_;
goto v___jp_2017_;
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref_known(v_a_2161_, 1);
lean_dec(v_a_2150_);
lean_dec(v_a_2145_);
lean_dec(v_val_2137_);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2175_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2172_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2172_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
uint8_t v___x_2183_; 
lean_dec(v_a_2165_);
v___x_2183_ = lean_unbox(v_a_2120_);
lean_dec(v_a_2120_);
lean_inc(v_a_2145_);
lean_inc(v_a_2150_);
v___y_2018_ = v_a_2126_;
v___y_2019_ = v_val_2137_;
v___y_2020_ = v_a_2150_;
v___y_2021_ = v_binderType_2088_;
v___y_2022_ = v_a_2145_;
v___y_2023_ = v___x_2183_;
v___y_2024_ = v_a_2150_;
v___y_2025_ = v_a_2161_;
v___y_2026_ = v_a_2145_;
v_neutral_2027_ = v_a_2163_;
v___y_2028_ = v___y_2071_;
v___y_2029_ = v___y_2072_;
v___y_2030_ = v___y_2073_;
v___y_2031_ = v___y_2074_;
v___y_2032_ = v___y_2075_;
v___y_2033_ = v___y_2076_;
v___y_2034_ = v___y_2077_;
v___y_2035_ = v___y_2078_;
v___y_2036_ = v___y_2079_;
v___y_2037_ = v___y_2080_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_a_2163_);
lean_dec_ref_known(v_a_2161_, 1);
lean_dec(v_a_2150_);
lean_dec(v_a_2145_);
lean_dec(v_val_2137_);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2184_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2164_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2164_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
lean_dec(v_a_2161_);
lean_dec(v_a_2156_);
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_unbox(v_a_2120_);
lean_dec(v_a_2120_);
lean_inc(v_a_2145_);
lean_inc(v_a_2150_);
v___y_1962_ = v_a_2126_;
v___y_1963_ = v_val_2137_;
v___y_1964_ = v_a_2150_;
v___y_1965_ = v_binderType_2088_;
v___y_1966_ = v_a_2145_;
v___y_1967_ = v___x_2193_;
v___y_1968_ = v_a_2150_;
v___y_1969_ = v_a_2145_;
v_fst_1970_ = v___x_2192_;
v_snd_1971_ = v___x_2192_;
v___y_1972_ = v___y_2071_;
v___y_1973_ = v___y_2072_;
v___y_1974_ = v___y_2073_;
v___y_1975_ = v___y_2074_;
v___y_1976_ = v___y_2075_;
v___y_1977_ = v___y_2076_;
v___y_1978_ = v___y_2077_;
v___y_1979_ = v___y_2078_;
v___y_1980_ = v___y_2079_;
v___y_1981_ = v___y_2080_;
goto v___jp_1961_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_a_2156_);
lean_dec(v_a_2150_);
lean_dec(v_a_2145_);
lean_dec(v_val_2137_);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2194_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2160_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2160_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_a_2150_);
lean_dec(v_a_2145_);
lean_dec(v_val_2137_);
lean_dec_ref_known(v___x_2129_, 2);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2202_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2155_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2155_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_a_2145_);
lean_del_object(v___x_2139_);
lean_dec(v_val_2137_);
lean_dec_ref_known(v___x_2129_, 2);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2211_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2149_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2149_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_del_object(v___x_2139_);
lean_dec(v_val_2137_);
lean_dec_ref_known(v___x_2129_, 2);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2219_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2144_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2144_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
lean_dec(v_a_2133_);
lean_dec_ref_known(v___x_2129_, 2);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v___x_2228_ = lean_box(0);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2228_);
v___x_2230_ = v___x_2135_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref_known(v___x_2129_, 2);
lean_dec(v_a_2126_);
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2233_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2132_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2132_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2241_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2125_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2125_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_dec(v_a_2120_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v___x_2249_ = lean_box(0);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2249_);
v___x_2251_ = v___x_2122_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_op_1848_);
v_a_2254_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2119_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2119_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v_a_2263_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2109_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2109_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec_ref(v_body_2097_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v_a_2272_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2099_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2099_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_dec_ref(v_body_2097_);
lean_dec_ref(v_binderType_2096_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2280_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2280_);
v___x_2282_ = v___x_2094_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec(v_a_2092_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2284_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2284_);
v___x_2286_ = v___x_2094_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v_a_2289_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2091_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2091_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
lean_dec_ref(v_body_2089_);
lean_dec_ref(v_binderType_2088_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2297_ = lean_box(0);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2297_);
v___x_2299_ = v___x_2086_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_dec(v_a_2084_);
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v___x_2301_ = lean_box(0);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2301_);
v___x_2303_ = v___x_2086_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v_a_2306_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2083_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2083_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v_f_2069_);
lean_dec_ref(v_op_1848_);
v_a_2314_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2081_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2081_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* v_op_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec(v_a_2328_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* v_cls_2340_, lean_object* v_msg_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_2340_, v_msg_2341_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* v_cls_2354_, lean_object* v_msg_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2354_, v_msg_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec(v___y_2356_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* v_00_u03b2_2368_, lean_object* v_m_2369_, lean_object* v_a_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_2369_, v_a_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_m_2373_, lean_object* v_a_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_2372_, v_m_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_m_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2(lean_object* v_00_u03b2_2377_, lean_object* v_m_2378_, lean_object* v_query_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___redArg(v_m_2378_, v_query_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_m_2382_, lean_object* v_query_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_spec__2(v_00_u03b2_2381_, v_m_2382_, v_query_2383_);
lean_dec(v_query_2383_);
lean_dec_ref(v_m_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* v_op_2385_, lean_object* v_a_2386_, lean_object* v_s_2387_){
_start:
{
lean_object* v_structs_2388_; lean_object* v_opIdOf_2389_; lean_object* v_exprToOpIds_2390_; lean_object* v_steps_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_structs_2388_ = lean_ctor_get(v_s_2387_, 0);
v_opIdOf_2389_ = lean_ctor_get(v_s_2387_, 1);
v_exprToOpIds_2390_ = lean_ctor_get(v_s_2387_, 2);
v_steps_2391_ = lean_ctor_get(v_s_2387_, 3);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_s_2387_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v_s_2387_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_steps_2391_);
lean_inc(v_exprToOpIds_2390_);
lean_inc(v_opIdOf_2389_);
lean_inc(v_structs_2388_);
lean_dec(v_s_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_2389_, v_op_2385_, v_a_2386_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_structs_2388_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_exprToOpIds_2390_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_steps_2391_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* v_op_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2401_, v_a_2409_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2444_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2444_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2444_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v_opIdOf_2417_; lean_object* v___x_2418_; 
v_opIdOf_2417_ = lean_ctor_get(v_a_2413_, 1);
lean_inc_ref(v_opIdOf_2417_);
lean_dec(v_a_2413_);
v___x_2418_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_2417_, v_op_2400_);
lean_dec_ref(v_opIdOf_2417_);
if (lean_obj_tag(v___x_2418_) == 1)
{
lean_object* v_val_2419_; lean_object* v___x_2421_; 
lean_dec_ref(v_op_2400_);
v_val_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_val_2419_);
lean_dec_ref_known(v___x_2418_, 1);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v_val_2419_);
v___x_2421_ = v___x_2415_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_val_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
else
{
lean_object* v___x_2423_; 
lean_dec(v___x_2418_);
lean_del_object(v___x_2415_);
lean_inc_ref(v_op_2400_);
v___x_2423_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc_n(v_a_2424_, 2);
lean_dec_ref_known(v___x_2423_, 1);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2425_, 0, v_op_2400_);
lean_closure_set(v___f_2425_, 1, v_a_2424_);
v___x_2426_ = l_Lean_Meta_Grind_AC_acExt;
v___x_2427_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2426_, v___f_2425_, v_a_2401_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v___x_2427_, 0);
lean_dec(v_unused_2435_);
v___x_2429_ = v___x_2427_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v___x_2427_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v_a_2424_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2424_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2424_);
v_a_2436_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_dec_ref(v_op_2400_);
return v___x_2423_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_op_2400_);
v_a_2445_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2412_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2412_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* v_op_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec(v_a_2454_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* v_e_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
uint8_t v___y_2480_; uint8_t v___x_2513_; 
v___x_2513_ = l_Lean_Expr_isApp(v_e_2466_);
if (v___x_2513_ == 0)
{
v___y_2480_ = v___x_2513_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = l_Lean_Expr_appFn_x21(v_e_2466_);
v___x_2515_ = l_Lean_Expr_isApp(v___x_2514_);
lean_dec_ref(v___x_2514_);
v___y_2480_ = v___x_2515_;
goto v___jp_2479_;
}
v___jp_2479_:
{
if (v___y_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_box(0);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_Grind_AC_getOp(v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2504_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2504_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2504_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; uint8_t v___x_2492_; 
v___x_2488_ = l_Lean_Expr_appFn_x21(v_e_2466_);
v___x_2489_ = l_Lean_Expr_appFn_x21(v___x_2488_);
v___x_2490_ = lean_ptr_addr(v___x_2489_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = lean_ptr_addr(v_a_2484_);
lean_dec(v_a_2484_);
v___x_2492_ = lean_usize_dec_eq(v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
lean_dec_ref(v___x_2488_);
v___x_2493_ = lean_box(0);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2493_);
v___x_2495_ = v___x_2486_;
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
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2497_ = l_Lean_Expr_appArg_x21(v___x_2488_);
lean_dec_ref(v___x_2488_);
v___x_2498_ = l_Lean_Expr_appArg_x21(v_e_2466_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2500_);
v___x_2502_ = v___x_2486_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2505_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2483_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2483_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* v_e_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_e_2516_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2558_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_commInst_x3f_2547_; 
v_commInst_x3f_2547_ = lean_ctor_get(v_a_2543_, 7);
lean_inc(v_commInst_x3f_2547_);
lean_dec(v_a_2543_);
if (lean_obj_tag(v_commInst_x3f_2547_) == 0)
{
uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = 0;
v___x_2549_ = lean_box(v___x_2548_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2549_);
v___x_2551_ = v___x_2545_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
else
{
uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec_ref_known(v_commInst_x3f_2547_, 1);
v___x_2553_ = 1;
v___x_2554_ = lean_box(v___x_2553_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2554_);
v___x_2556_ = v___x_2545_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2542_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2542_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2608_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2608_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2608_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_neutralInst_x3f_2597_; 
v_neutralInst_x3f_2597_ = lean_ctor_get(v_a_2593_, 8);
lean_inc(v_neutralInst_x3f_2597_);
lean_dec(v_a_2593_);
if (lean_obj_tag(v_neutralInst_x3f_2597_) == 0)
{
uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2598_ = 0;
v___x_2599_ = lean_box(v___x_2598_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2599_);
v___x_2601_ = v___x_2595_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
else
{
uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec_ref_known(v_neutralInst_x3f_2597_, 1);
v___x_2603_ = 1;
v___x_2604_ = lean_box(v___x_2603_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2604_);
v___x_2606_ = v___x_2595_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2592_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2592_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec_ref(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec(v_a_2617_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2658_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2658_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2658_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_idempotentInst_x3f_2647_; 
v_idempotentInst_x3f_2647_ = lean_ctor_get(v_a_2643_, 6);
lean_inc(v_idempotentInst_x3f_2647_);
lean_dec(v_a_2643_);
if (lean_obj_tag(v_idempotentInst_x3f_2647_) == 0)
{
uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = 0;
v___x_2649_ = lean_box(v___x_2648_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2649_);
v___x_2651_ = v___x_2645_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
else
{
uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec_ref_known(v_idempotentInst_x3f_2647_, 1);
v___x_2653_ = 1;
v___x_2654_ = lean_box(v___x_2653_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2654_);
v___x_2656_ = v___x_2645_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2642_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2642_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec(v_a_2667_);
return v_res_2679_;
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
