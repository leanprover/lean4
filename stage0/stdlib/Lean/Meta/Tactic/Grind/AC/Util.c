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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0;
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v___x_74_);
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
v_acSteps_81_ = lean_ctor_get(v_a_77_, 7);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_519_; uint64_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1723u);
v___x_520_ = lean_uint64_of_nat(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
return v_x_521_;
}
else
{
lean_object* v_key_523_; lean_object* v_value_524_; lean_object* v_tail_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_551_; 
v_key_523_ = lean_ctor_get(v_x_522_, 0);
v_value_524_ = lean_ctor_get(v_x_522_, 1);
v_tail_525_ = lean_ctor_get(v_x_522_, 2);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_551_ == 0)
{
v___x_527_ = v_x_522_;
v_isShared_528_ = v_isSharedCheck_551_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_tail_525_);
lean_inc(v_value_524_);
lean_inc(v_key_523_);
lean_dec(v_x_522_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_551_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; uint64_t v___y_531_; 
v___x_529_ = lean_array_get_size(v_x_521_);
if (lean_obj_tag(v_key_523_) == 0)
{
uint64_t v___x_549_; 
v___x_549_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_531_ = v___x_549_;
goto v___jp_530_;
}
else
{
uint64_t v_hash_550_; 
v_hash_550_ = lean_ctor_get_uint64(v_key_523_, sizeof(void*)*2);
v___y_531_ = v_hash_550_;
goto v___jp_530_;
}
v___jp_530_:
{
uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v_fold_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_532_ = 32ULL;
v___x_533_ = lean_uint64_shift_right(v___y_531_, v___x_532_);
v_fold_534_ = lean_uint64_xor(v___y_531_, v___x_533_);
v___x_535_ = 16ULL;
v___x_536_ = lean_uint64_shift_right(v_fold_534_, v___x_535_);
v___x_537_ = lean_uint64_xor(v_fold_534_, v___x_536_);
v___x_538_ = lean_uint64_to_usize(v___x_537_);
v___x_539_ = lean_usize_of_nat(v___x_529_);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_sub(v___x_539_, v___x_540_);
v___x_542_ = lean_usize_land(v___x_538_, v___x_541_);
v___x_543_ = lean_array_uget_borrowed(v_x_521_, v___x_542_);
lean_inc(v___x_543_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 2, v___x_543_);
v___x_545_ = v___x_527_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_key_523_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_value_524_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v___x_543_);
v___x_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = lean_array_uset(v_x_521_, v___x_542_, v___x_545_);
v_x_521_ = v___x_546_;
v_x_522_ = v_tail_525_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_552_, lean_object* v_source_553_, lean_object* v_target_554_){
_start:
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_array_get_size(v_source_553_);
v___x_556_ = lean_nat_dec_lt(v_i_552_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec_ref(v_source_553_);
lean_dec(v_i_552_);
return v_target_554_;
}
else
{
lean_object* v_es_557_; lean_object* v___x_558_; lean_object* v_source_559_; lean_object* v_target_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_es_557_ = lean_array_fget(v_source_553_, v_i_552_);
v___x_558_ = lean_box(0);
v_source_559_ = lean_array_fset(v_source_553_, v_i_552_, v___x_558_);
v_target_560_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_554_, v_es_557_);
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_add(v_i_552_, v___x_561_);
lean_dec(v_i_552_);
v_i_552_ = v___x_562_;
v_source_553_ = v_source_559_;
v_target_554_ = v_target_560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object* v_data_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_nbuckets_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_565_ = lean_array_get_size(v_data_564_);
v___x_566_ = lean_unsigned_to_nat(2u);
v_nbuckets_567_ = lean_nat_mul(v___x_565_, v___x_566_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_box(0);
v___x_570_ = lean_mk_array(v_nbuckets_567_, v___x_569_);
v___x_571_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_568_, v_data_564_, v___x_570_);
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
v___x_627_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* v_op_790_, lean_object* v_f_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_794_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_879_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_879_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_879_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_879_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v_ring_812_; uint8_t v___y_814_; lean_object* v___y_815_; 
v_ring_812_ = lean_ctor_get_uint8(v_a_808_, sizeof(void*)*12 + 21);
lean_dec(v_a_808_);
if (v_ring_812_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_box(v_ring_812_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_859_);
v___x_861_ = v___x_810_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
if (lean_obj_tag(v_f_791_) == 4)
{
lean_object* v_declName_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
lean_del_object(v___x_810_);
v_declName_863_ = lean_ctor_get(v_f_791_, 0);
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2));
v___x_865_ = lean_name_eq(v_declName_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5));
v___x_867_ = lean_name_eq(v_declName_863_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8));
v___x_869_ = lean_name_eq(v_declName_863_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11));
v___x_871_ = lean_name_eq(v_declName_863_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14));
v___x_873_ = lean_name_eq(v_declName_863_, v___x_872_);
if (v___x_873_ == 0)
{
goto v___jp_803_;
}
else
{
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
}
else
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = 0;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_875_);
v___x_877_ = v___x_810_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
v___jp_813_:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v___y_815_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
if (lean_obj_tag(v_a_817_) == 0)
{
lean_del_object(v___x_819_);
goto v___jp_803_;
}
else
{
lean_dec_ref(v_a_817_);
if (v___y_814_ == 0)
{
lean_del_object(v___x_819_);
goto v___jp_803_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_box(v_ring_812_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_816_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
v___jp_834_:
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_835_ = l_Lean_Expr_getAppNumArgs(v_op_790_);
v___x_836_ = lean_unsigned_to_nat(4u);
v___x_837_ = lean_nat_dec_eq(v___x_835_, v___x_836_);
lean_dec(v___x_835_);
if (v___x_837_ == 0)
{
goto v___jp_803_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_Expr_appFn_x21(v_op_790_);
v___x_839_ = l_Lean_Expr_appFn_x21(v___x_838_);
lean_dec_ref(v___x_838_);
v___x_840_ = l_Lean_Expr_appArg_x21(v___x_839_);
lean_dec_ref(v___x_839_);
lean_inc_ref(v___x_840_);
v___x_841_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v___x_840_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 0)
{
lean_del_object(v___x_844_);
v___y_814_ = v___x_837_;
v___y_815_ = v___x_840_;
goto v___jp_813_;
}
else
{
lean_dec_ref(v_a_842_);
if (v___x_837_ == 0)
{
lean_del_object(v___x_844_);
v___y_814_ = v___x_837_;
v___y_815_ = v___x_840_;
goto v___jp_813_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_848_; 
lean_dec_ref(v___x_840_);
v___x_846_ = lean_box(v_ring_812_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___x_840_);
v_a_851_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_841_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_841_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_807_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_807_);
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
v___jp_803_:
{
uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = 0;
v___x_805_ = lean_box(v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* v_op_888_, lean_object* v_f_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_888_, v_f_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_f_889_);
lean_dec_ref(v_op_888_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_902_, lean_object* v_vals_903_, lean_object* v_i_904_, lean_object* v_k_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_keys_902_);
v___x_907_ = lean_nat_dec_lt(v_i_904_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
lean_dec(v_i_904_);
v___x_908_ = lean_box(0);
return v___x_908_;
}
else
{
lean_object* v_k_x27_909_; uint8_t v___x_910_; 
v_k_x27_909_ = lean_array_fget_borrowed(v_keys_902_, v_i_904_);
v___x_910_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_905_, v_k_x27_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_904_, v___x_911_);
lean_dec(v_i_904_);
v_i_904_ = v___x_912_;
goto _start;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_array_fget_borrowed(v_vals_903_, v_i_904_);
lean_dec(v_i_904_);
lean_inc(v___x_914_);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_i_918_, lean_object* v_k_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_916_, v_vals_917_, v_i_918_, v_k_919_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_vals_917_);
lean_dec_ref(v_keys_916_);
return v_res_920_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; 
v___x_921_ = ((size_t)5ULL);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_shift_left(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; 
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0);
v___x_926_ = lean_usize_sub(v___x_925_, v___x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* v_x_927_, size_t v_x_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_es_930_; lean_object* v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_j_935_; lean_object* v___x_936_; 
v_es_930_ = lean_ctor_get(v_x_927_, 0);
v___x_931_ = lean_box(2);
v___x_932_ = ((size_t)5ULL);
v___x_933_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
v___x_934_ = lean_usize_land(v_x_928_, v___x_933_);
v_j_935_ = lean_usize_to_nat(v___x_934_);
v___x_936_ = lean_array_get_borrowed(v___x_931_, v_es_930_, v_j_935_);
lean_dec(v_j_935_);
switch(lean_obj_tag(v___x_936_))
{
case 0:
{
lean_object* v_key_937_; lean_object* v_val_938_; uint8_t v___x_939_; 
v_key_937_ = lean_ctor_get(v___x_936_, 0);
v_val_938_ = lean_ctor_get(v___x_936_, 1);
v___x_939_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_929_, v_key_937_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
lean_inc(v_val_938_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_val_938_);
return v___x_941_;
}
}
case 1:
{
lean_object* v_node_942_; size_t v___x_943_; 
v_node_942_ = lean_ctor_get(v___x_936_, 0);
v___x_943_ = lean_usize_shift_right(v_x_928_, v___x_932_);
v_x_927_ = v_node_942_;
v_x_928_ = v___x_943_;
goto _start;
}
default: 
{
lean_object* v___x_945_; 
v___x_945_ = lean_box(0);
return v___x_945_;
}
}
}
else
{
lean_object* v_ks_946_; lean_object* v_vs_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_ks_946_ = lean_ctor_get(v_x_927_, 0);
v_vs_947_ = lean_ctor_get(v_x_927_, 1);
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_946_, v_vs_947_, v___x_948_, v_x_929_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
size_t v_x_949__boxed_953_; lean_object* v_res_954_; 
v_x_949__boxed_953_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_954_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_950_, v_x_949__boxed_953_, v_x_952_);
lean_dec_ref(v_x_952_);
lean_dec_ref(v_x_950_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
uint64_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_956_);
v___x_958_ = lean_uint64_to_usize(v___x_957_);
v___x_959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_955_, v___x_958_, v_x_956_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_960_, v_x_961_);
lean_dec_ref(v_x_961_);
lean_dec_ref(v_x_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_982_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_982_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_982_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_exprToOpIds_972_; lean_object* v___x_973_; 
v_exprToOpIds_972_ = lean_ctor_get(v_a_968_, 2);
lean_inc_ref(v_exprToOpIds_972_);
lean_dec(v_a_968_);
v___x_973_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_972_, v_e_963_);
lean_dec_ref(v_exprToOpIds_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_974_);
v___x_976_ = v___x_970_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v_val_978_; lean_object* v___x_980_; 
v_val_978_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_val_978_);
lean_dec_ref(v___x_973_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_val_978_);
v___x_980_ = v___x_970_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_val_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_967_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_967_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_991_, v_a_992_, v_a_993_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_e_991_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_996_, v_a_997_, v_a_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* v_e_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_e_1009_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(v_00_u03b2_1026_, v_x_1027_, v_x_1028_);
lean_dec_ref(v_x_1028_);
lean_dec_ref(v_x_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* v_00_u03b2_1030_, lean_object* v_x_1031_, size_t v_x_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1031_, v_x_1032_, v_x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
size_t v_x_1076__boxed_1039_; lean_object* v_res_1040_; 
v_x_1076__boxed_1039_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_res_1040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_1035_, v_x_1036_, v_x_1076__boxed_1039_, v_x_1038_);
lean_dec_ref(v_x_1038_);
lean_dec_ref(v_x_1036_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1041_, lean_object* v_keys_1042_, lean_object* v_vals_1043_, lean_object* v_heq_1044_, lean_object* v_i_1045_, lean_object* v_k_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1042_, v_vals_1043_, v_i_1045_, v_k_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1048_, lean_object* v_keys_1049_, lean_object* v_vals_1050_, lean_object* v_heq_1051_, lean_object* v_i_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_1048_, v_keys_1049_, v_vals_1050_, v_heq_1051_, v_i_1052_, v_k_1053_);
lean_dec_ref(v_k_1053_);
lean_dec_ref(v_vals_1050_);
lean_dec_ref(v_keys_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* v_opId_1055_, lean_object* v_a_1056_){
_start:
{
if (lean_obj_tag(v_a_1056_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_opId_1055_);
lean_ctor_set(v___x_1057_, 1, v_a_1056_);
return v___x_1057_;
}
else
{
lean_object* v_head_1058_; lean_object* v_tail_1059_; uint8_t v___x_1060_; 
v_head_1058_ = lean_ctor_get(v_a_1056_, 0);
v_tail_1059_ = lean_ctor_get(v_a_1056_, 1);
v___x_1060_ = lean_nat_dec_lt(v_opId_1055_, v_head_1058_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1072_; 
lean_inc(v_tail_1059_);
lean_inc(v_head_1058_);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_a_1056_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; lean_object* v_unused_1074_; 
v_unused_1073_ = lean_ctor_get(v_a_1056_, 1);
lean_dec(v_unused_1073_);
v_unused_1074_ = lean_ctor_get(v_a_1056_, 0);
lean_dec(v_unused_1074_);
v___x_1062_ = v_a_1056_;
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v_a_1056_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1072_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_nat_dec_eq(v_opId_1055_, v_head_1058_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1055_, v_tail_1059_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_head_1058_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_head_1058_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_opId_1055_);
v___x_1070_ = v___x_1062_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_opId_1055_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_tail_1059_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_opId_1055_);
lean_ctor_set(v___x_1075_, 1, v_a_1056_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v_ks_1080_; lean_object* v_vs_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1105_; 
v_ks_1080_ = lean_ctor_get(v_x_1076_, 0);
v_vs_1081_ = lean_ctor_get(v_x_1076_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1076_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1083_ = v_x_1076_;
v_isShared_1084_ = v_isSharedCheck_1105_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_vs_1081_);
lean_inc(v_ks_1080_);
lean_dec(v_x_1076_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1105_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = lean_array_get_size(v_ks_1080_);
v___x_1086_ = lean_nat_dec_lt(v_x_1077_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec(v_x_1077_);
v___x_1087_ = lean_array_push(v_ks_1080_, v_x_1078_);
v___x_1088_ = lean_array_push(v_vs_1081_, v_x_1079_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1088_);
lean_ctor_set(v___x_1083_, 0, v___x_1087_);
v___x_1090_ = v___x_1083_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
lean_object* v_k_x27_1092_; uint8_t v___x_1093_; 
v_k_x27_1092_ = lean_array_fget_borrowed(v_ks_1080_, v_x_1077_);
v___x_1093_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1078_, v_k_x27_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1095_; 
if (v_isShared_1084_ == 0)
{
v___x_1095_ = v___x_1083_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_ks_1080_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_vs_1081_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_x_1077_, v___x_1096_);
lean_dec(v_x_1077_);
v_x_1076_ = v___x_1095_;
v_x_1077_ = v___x_1097_;
goto _start;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = lean_array_fset(v_ks_1080_, v_x_1077_, v_x_1078_);
v___x_1101_ = lean_array_fset(v_vs_1081_, v_x_1077_, v_x_1079_);
lean_dec(v_x_1077_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1101_);
lean_ctor_set(v___x_1083_, 0, v___x_1100_);
v___x_1103_ = v___x_1083_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1101_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1106_, lean_object* v_k_1107_, lean_object* v_v_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1106_, v___x_1109_, v_k_1107_, v_v_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* v_x_1112_, size_t v_x_1113_, size_t v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_es_1117_; size_t v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; lean_object* v_j_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_es_1117_ = lean_ctor_get(v_x_1112_, 0);
v___x_1118_ = ((size_t)5ULL);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
v___x_1121_ = lean_usize_land(v_x_1113_, v___x_1120_);
v_j_1122_ = lean_usize_to_nat(v___x_1121_);
v___x_1123_ = lean_array_get_size(v_es_1117_);
v___x_1124_ = lean_nat_dec_lt(v_j_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec(v_j_1122_);
lean_dec(v_x_1116_);
lean_dec_ref(v_x_1115_);
return v_x_1112_;
}
else
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1161_; 
lean_inc_ref(v_es_1117_);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_x_1112_, 0);
lean_dec(v_unused_1162_);
v___x_1126_ = v_x_1112_;
v_isShared_1127_ = v_isSharedCheck_1161_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_x_1112_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1161_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_v_1128_; lean_object* v___x_1129_; lean_object* v_xs_x27_1130_; lean_object* v___y_1132_; 
v_v_1128_ = lean_array_fget(v_es_1117_, v_j_1122_);
v___x_1129_ = lean_box(0);
v_xs_x27_1130_ = lean_array_fset(v_es_1117_, v_j_1122_, v___x_1129_);
switch(lean_obj_tag(v_v_1128_))
{
case 0:
{
lean_object* v_key_1137_; lean_object* v_val_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_key_1137_ = lean_ctor_get(v_v_1128_, 0);
v_val_1138_ = lean_ctor_get(v_v_1128_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_v_1128_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1140_ = v_v_1128_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_val_1138_);
lean_inc(v_key_1137_);
lean_dec(v_v_1128_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
uint8_t v___x_1142_; 
v___x_1142_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1115_, v_key_1137_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_del_object(v___x_1140_);
v___x_1143_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1137_, v_val_1138_, v_x_1115_, v_x_1116_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___y_1132_ = v___x_1144_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1146_; 
lean_dec(v_val_1138_);
lean_dec(v_key_1137_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v_x_1116_);
lean_ctor_set(v___x_1140_, 0, v_x_1115_);
v___x_1146_ = v___x_1140_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_x_1115_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_x_1116_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v___y_1132_ = v___x_1146_;
goto v___jp_1131_;
}
}
}
}
case 1:
{
lean_object* v_node_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_node_1149_ = lean_ctor_get(v_v_1128_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_v_1128_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v_v_1128_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_node_1149_);
lean_dec(v_v_1128_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1153_ = lean_usize_shift_right(v_x_1113_, v___x_1118_);
v___x_1154_ = lean_usize_add(v_x_1114_, v___x_1119_);
v___x_1155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_1149_, v___x_1153_, v___x_1154_, v_x_1115_, v_x_1116_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
v___y_1132_ = v___x_1157_;
goto v___jp_1131_;
}
}
}
default: 
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_x_1115_);
lean_ctor_set(v___x_1160_, 1, v_x_1116_);
v___y_1132_ = v___x_1160_;
goto v___jp_1131_;
}
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_array_fset(v_xs_x27_1130_, v_j_1122_, v___y_1132_);
lean_dec(v_j_1122_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1133_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
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
lean_object* v_ks_1163_; lean_object* v_vs_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1184_; 
v_ks_1163_ = lean_ctor_get(v_x_1112_, 0);
v_vs_1164_ = lean_ctor_get(v_x_1112_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1166_ = v_x_1112_;
v_isShared_1167_ = v_isSharedCheck_1184_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_vs_1164_);
lean_inc(v_ks_1163_);
lean_dec(v_x_1112_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1184_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_ks_1163_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_vs_1164_);
v___x_1169_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v_newNode_1170_; uint8_t v___y_1172_; size_t v___x_1178_; uint8_t v___x_1179_; 
v_newNode_1170_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_1169_, v_x_1115_, v_x_1116_);
v___x_1178_ = ((size_t)7ULL);
v___x_1179_ = lean_usize_dec_le(v___x_1178_, v_x_1114_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1170_);
v___x_1181_ = lean_unsigned_to_nat(4u);
v___x_1182_ = lean_nat_dec_lt(v___x_1180_, v___x_1181_);
lean_dec(v___x_1180_);
v___y_1172_ = v___x_1182_;
goto v___jp_1171_;
}
else
{
v___y_1172_ = v___x_1179_;
goto v___jp_1171_;
}
v___jp_1171_:
{
if (v___y_1172_ == 0)
{
lean_object* v_ks_1173_; lean_object* v_vs_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_ks_1173_ = lean_ctor_get(v_newNode_1170_, 0);
lean_inc_ref(v_ks_1173_);
v_vs_1174_ = lean_ctor_get(v_newNode_1170_, 1);
lean_inc_ref(v_vs_1174_);
lean_dec_ref(v_newNode_1170_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
v___x_1177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_1114_, v_ks_1173_, v_vs_1174_, v___x_1175_, v___x_1176_);
lean_dec_ref(v_vs_1174_);
lean_dec_ref(v_ks_1173_);
return v___x_1177_;
}
else
{
return v_newNode_1170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1185_, lean_object* v_keys_1186_, lean_object* v_vals_1187_, lean_object* v_i_1188_, lean_object* v_entries_1189_){
_start:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_get_size(v_keys_1186_);
v___x_1191_ = lean_nat_dec_lt(v_i_1188_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_dec(v_i_1188_);
return v_entries_1189_;
}
else
{
lean_object* v_k_1192_; lean_object* v_v_1193_; uint64_t v___x_1194_; size_t v_h_1195_; size_t v___x_1196_; lean_object* v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v_h_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_k_1192_ = lean_array_fget_borrowed(v_keys_1186_, v_i_1188_);
v_v_1193_ = lean_array_fget_borrowed(v_vals_1187_, v_i_1188_);
v___x_1194_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1192_);
v_h_1195_ = lean_uint64_to_usize(v___x_1194_);
v___x_1196_ = ((size_t)5ULL);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = ((size_t)1ULL);
v___x_1199_ = lean_usize_sub(v_depth_1185_, v___x_1198_);
v___x_1200_ = lean_usize_mul(v___x_1196_, v___x_1199_);
v_h_1201_ = lean_usize_shift_right(v_h_1195_, v___x_1200_);
v___x_1202_ = lean_nat_add(v_i_1188_, v___x_1197_);
lean_dec(v_i_1188_);
lean_inc(v_v_1193_);
lean_inc(v_k_1192_);
v___x_1203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_1189_, v_h_1201_, v_depth_1185_, v_k_1192_, v_v_1193_);
v_i_1188_ = v___x_1202_;
v_entries_1189_ = v___x_1203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1205_, lean_object* v_keys_1206_, lean_object* v_vals_1207_, lean_object* v_i_1208_, lean_object* v_entries_1209_){
_start:
{
size_t v_depth_boxed_1210_; lean_object* v_res_1211_; 
v_depth_boxed_1210_ = lean_unbox_usize(v_depth_1205_);
lean_dec(v_depth_1205_);
v_res_1211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1210_, v_keys_1206_, v_vals_1207_, v_i_1208_, v_entries_1209_);
lean_dec_ref(v_vals_1207_);
lean_dec_ref(v_keys_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_x_1216_){
_start:
{
size_t v_x_398__boxed_1217_; size_t v_x_399__boxed_1218_; lean_object* v_res_1219_; 
v_x_398__boxed_1217_ = lean_unbox_usize(v_x_1213_);
lean_dec(v_x_1213_);
v_x_399__boxed_1218_ = lean_unbox_usize(v_x_1214_);
lean_dec(v_x_1214_);
v_res_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1212_, v_x_398__boxed_1217_, v_x_399__boxed_1218_, v_x_1215_, v_x_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
uint64_t v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1221_);
v___x_1224_ = lean_uint64_to_usize(v___x_1223_);
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1220_, v___x_1224_, v___x_1225_, v_x_1221_, v_x_1222_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* v_m_1227_, lean_object* v_e_1228_, lean_object* v_opId_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_m_1227_, v_e_1228_);
if (lean_obj_tag(v___x_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_val_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1229_, v_val_1231_);
v___x_1233_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1227_, v_e_1228_, v___x_1232_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v___x_1230_);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_opId_1229_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1227_, v_e_1228_, v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* v_00_u03b2_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_1238_, v_x_1239_, v_x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* v_00_u03b2_1242_, lean_object* v_x_1243_, size_t v_x_1244_, size_t v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1243_, v_x_1244_, v_x_1245_, v_x_1246_, v_x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
size_t v_x_590__boxed_1255_; size_t v_x_591__boxed_1256_; lean_object* v_res_1257_; 
v_x_590__boxed_1255_ = lean_unbox_usize(v_x_1251_);
lean_dec(v_x_1251_);
v_x_591__boxed_1256_ = lean_unbox_usize(v_x_1252_);
lean_dec(v_x_1252_);
v_res_1257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_1249_, v_x_1250_, v_x_590__boxed_1255_, v_x_591__boxed_1256_, v_x_1253_, v_x_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1258_, lean_object* v_n_1259_, lean_object* v_k_1260_, lean_object* v_v_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_1259_, v_k_1260_, v_v_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1263_, size_t v_depth_1264_, lean_object* v_keys_1265_, lean_object* v_vals_1266_, lean_object* v_heq_1267_, lean_object* v_i_1268_, lean_object* v_entries_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1264_, v_keys_1265_, v_vals_1266_, v_i_1268_, v_entries_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1271_, lean_object* v_depth_1272_, lean_object* v_keys_1273_, lean_object* v_vals_1274_, lean_object* v_heq_1275_, lean_object* v_i_1276_, lean_object* v_entries_1277_){
_start:
{
size_t v_depth_boxed_1278_; lean_object* v_res_1279_; 
v_depth_boxed_1278_ = lean_unbox_usize(v_depth_1272_);
lean_dec(v_depth_1272_);
v_res_1279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_1271_, v_depth_boxed_1278_, v_keys_1273_, v_vals_1274_, v_heq_1275_, v_i_1276_, v_entries_1277_);
lean_dec_ref(v_vals_1274_);
lean_dec_ref(v_keys_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1281_, v_x_1282_, v_x_1283_, v_x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_s_1288_){
_start:
{
lean_object* v_structs_1289_; lean_object* v_opIdOf_1290_; lean_object* v_exprToOpIds_1291_; lean_object* v_steps_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
v_structs_1289_ = lean_ctor_get(v_s_1288_, 0);
v_opIdOf_1290_ = lean_ctor_get(v_s_1288_, 1);
v_exprToOpIds_1291_ = lean_ctor_get(v_s_1288_, 2);
v_steps_1292_ = lean_ctor_get(v_s_1288_, 3);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_s_1288_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v_s_1288_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_steps_1292_);
lean_inc(v_exprToOpIds_1291_);
lean_inc(v_opIdOf_1290_);
lean_inc(v_structs_1289_);
lean_dec(v_s_1288_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_inc(v_a_1287_);
v___x_1296_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(v_exprToOpIds_1291_, v_e_1286_, v_a_1287_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 2, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_structs_1289_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_opIdOf_1290_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_steps_1292_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object* v_e_1301_, lean_object* v_a_1302_, lean_object* v_s_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_1301_, v_a_1302_, v_s_1303_);
lean_dec(v_a_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v___f_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_inc(v_a_1306_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1309_, 0, v_e_1305_);
lean_closure_set(v___f_1309_, 1, v_a_1306_);
v___x_1310_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1311_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1310_, v___f_1309_, v_a_1307_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* v_e_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_a_1314_);
lean_dec(v_a_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1317_, v_a_1318_, v_a_1319_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec(v_a_1332_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* v_e_1345_, lean_object* v_size_1346_, lean_object* v_s_1347_){
_start:
{
lean_object* v_id_1348_; lean_object* v_type_1349_; lean_object* v_u_1350_; lean_object* v_op_1351_; lean_object* v_neutral_x3f_1352_; lean_object* v_assocInst_1353_; lean_object* v_idempotentInst_x3f_1354_; lean_object* v_commInst_x3f_1355_; lean_object* v_neutralInst_x3f_1356_; lean_object* v_nextId_1357_; lean_object* v_vars_1358_; lean_object* v_varMap_1359_; lean_object* v_denote_1360_; lean_object* v_denoteEntries_1361_; lean_object* v_queue_1362_; lean_object* v_basis_1363_; lean_object* v_diseqs_1364_; uint8_t v_recheck_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1374_; 
v_id_1348_ = lean_ctor_get(v_s_1347_, 0);
v_type_1349_ = lean_ctor_get(v_s_1347_, 1);
v_u_1350_ = lean_ctor_get(v_s_1347_, 2);
v_op_1351_ = lean_ctor_get(v_s_1347_, 3);
v_neutral_x3f_1352_ = lean_ctor_get(v_s_1347_, 4);
v_assocInst_1353_ = lean_ctor_get(v_s_1347_, 5);
v_idempotentInst_x3f_1354_ = lean_ctor_get(v_s_1347_, 6);
v_commInst_x3f_1355_ = lean_ctor_get(v_s_1347_, 7);
v_neutralInst_x3f_1356_ = lean_ctor_get(v_s_1347_, 8);
v_nextId_1357_ = lean_ctor_get(v_s_1347_, 9);
v_vars_1358_ = lean_ctor_get(v_s_1347_, 10);
v_varMap_1359_ = lean_ctor_get(v_s_1347_, 11);
v_denote_1360_ = lean_ctor_get(v_s_1347_, 12);
v_denoteEntries_1361_ = lean_ctor_get(v_s_1347_, 13);
v_queue_1362_ = lean_ctor_get(v_s_1347_, 14);
v_basis_1363_ = lean_ctor_get(v_s_1347_, 15);
v_diseqs_1364_ = lean_ctor_get(v_s_1347_, 16);
v_recheck_1365_ = lean_ctor_get_uint8(v_s_1347_, sizeof(void*)*17);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_s_1347_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1367_ = v_s_1347_;
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_diseqs_1364_);
lean_inc(v_basis_1363_);
lean_inc(v_queue_1362_);
lean_inc(v_denoteEntries_1361_);
lean_inc(v_denote_1360_);
lean_inc(v_varMap_1359_);
lean_inc(v_vars_1358_);
lean_inc(v_nextId_1357_);
lean_inc(v_neutralInst_x3f_1356_);
lean_inc(v_commInst_x3f_1355_);
lean_inc(v_idempotentInst_x3f_1354_);
lean_inc(v_assocInst_1353_);
lean_inc(v_neutral_x3f_1352_);
lean_inc(v_op_1351_);
lean_inc(v_u_1350_);
lean_inc(v_type_1349_);
lean_inc(v_id_1348_);
lean_dec(v_s_1347_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1374_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_inc_ref(v_e_1345_);
v___x_1369_ = l_Lean_PersistentArray_push___redArg(v_vars_1358_, v_e_1345_);
v___x_1370_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_1359_, v_e_1345_, v_size_1346_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 11, v___x_1370_);
lean_ctor_set(v___x_1367_, 10, v___x_1369_);
v___x_1372_ = v___x_1367_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_id_1348_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_type_1349_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_u_1350_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_op_1351_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_neutral_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1373_, 5, v_assocInst_1353_);
lean_ctor_set(v_reuseFailAlloc_1373_, 6, v_idempotentInst_x3f_1354_);
lean_ctor_set(v_reuseFailAlloc_1373_, 7, v_commInst_x3f_1355_);
lean_ctor_set(v_reuseFailAlloc_1373_, 8, v_neutralInst_x3f_1356_);
lean_ctor_set(v_reuseFailAlloc_1373_, 9, v_nextId_1357_);
lean_ctor_set(v_reuseFailAlloc_1373_, 10, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 11, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1373_, 12, v_denote_1360_);
lean_ctor_set(v_reuseFailAlloc_1373_, 13, v_denoteEntries_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 14, v_queue_1362_);
lean_ctor_set(v_reuseFailAlloc_1373_, 15, v_basis_1363_);
lean_ctor_set(v_reuseFailAlloc_1373_, 16, v_diseqs_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, sizeof(void*)*17, v_recheck_1365_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1438_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1438_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1438_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_vars_1393_; lean_object* v_varMap_1394_; lean_object* v___x_1395_; 
v_vars_1393_ = lean_ctor_get(v_a_1389_, 10);
lean_inc_ref(v_vars_1393_);
v_varMap_1394_ = lean_ctor_get(v_a_1389_, 11);
lean_inc_ref(v_varMap_1394_);
lean_dec(v_a_1389_);
v___x_1395_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_1394_, v_e_1375_);
lean_dec_ref(v_varMap_1394_);
if (lean_obj_tag(v___x_1395_) == 1)
{
lean_object* v_val_1396_; lean_object* v___x_1398_; 
lean_dec_ref(v_vars_1393_);
lean_dec_ref(v_e_1375_);
v_val_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_val_1396_);
lean_dec_ref(v___x_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_val_1396_);
v___x_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_val_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
else
{
lean_object* v_size_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; 
lean_dec(v___x_1395_);
lean_del_object(v___x_1391_);
v_size_1400_ = lean_ctor_get(v_vars_1393_, 2);
lean_inc_n(v_size_1400_, 2);
lean_dec_ref(v_vars_1393_);
lean_inc_ref(v_e_1375_);
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(v___f_1401_, 0, v_e_1375_);
lean_closure_set(v___f_1401_, 1, v_size_1400_);
v___x_1402_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_1401_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; 
lean_dec_ref(v___x_1402_);
lean_inc_ref(v_e_1375_);
v___x_1403_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v___x_1403_);
v___x_1404_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1405_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1404_, v_e_1375_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1405_, 0);
lean_dec(v_unused_1413_);
v___x_1407_ = v___x_1405_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v___x_1405_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v_size_1400_);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_size_1400_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_size_1400_);
v_a_1414_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1405_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1405_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_size_1400_);
lean_dec_ref(v_e_1375_);
v_a_1422_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1403_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1403_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_size_1400_);
lean_dec_ref(v_e_1375_);
v_a_1430_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1402_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1402_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_e_1375_);
v_a_1439_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1388_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1388_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* v_e_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec(v_a_1448_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* v_e_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; lean_object* v_mctx_1465_; lean_object* v___x_1466_; lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1469_; lean_object* v_cache_1470_; lean_object* v_zetaDeltaFVarIds_1471_; lean_object* v_postponed_1472_; lean_object* v_diag_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v___x_1464_ = lean_st_ref_get(v___y_1462_);
v_mctx_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc_ref(v_mctx_1465_);
lean_dec(v___x_1464_);
v___x_1466_ = lean_instantiate_expr_mvars(v_mctx_1465_, v_e_1461_);
v_fst_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_fst_1467_);
v_snd_1468_ = lean_ctor_get(v___x_1466_, 1);
lean_inc(v_snd_1468_);
lean_dec_ref(v___x_1466_);
v___x_1469_ = lean_st_ref_take(v___y_1462_);
v_cache_1470_ = lean_ctor_get(v___x_1469_, 1);
v_zetaDeltaFVarIds_1471_ = lean_ctor_get(v___x_1469_, 2);
v_postponed_1472_ = lean_ctor_get(v___x_1469_, 3);
v_diag_1473_ = lean_ctor_get(v___x_1469_, 4);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1483_);
v___x_1475_ = v___x_1469_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_diag_1473_);
lean_inc(v_postponed_1472_);
lean_inc(v_zetaDeltaFVarIds_1471_);
lean_inc(v_cache_1470_);
lean_dec(v___x_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_fst_1467_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_fst_1467_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_cache_1470_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_zetaDeltaFVarIds_1471_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_postponed_1472_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_diag_1473_);
v___x_1478_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_st_ref_set(v___y_1462_, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_snd_1468_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* v_e_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1484_, v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* v_e_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1488_, v___y_1496_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* v_e_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec(v___y_1502_);
return v_res_1513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_unsigned_to_nat(32u);
v___x_1515_ = lean_mk_empty_array_with_capacity(v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1(void){
_start:
{
size_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1517_ = ((size_t)5ULL);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = lean_unsigned_to_nat(32u);
v___x_1520_ = lean_mk_empty_array_with_capacity(v___x_1519_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
v___x_1522_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1520_);
lean_ctor_set(v___x_1522_, 2, v___x_1518_);
lean_ctor_set(v___x_1522_, 3, v___x_1518_);
lean_ctor_set_usize(v___x_1522_, 4, v___x_1517_);
return v___x_1522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* v___x_1526_, lean_object* v_binderType_1527_, lean_object* v_a_1528_, lean_object* v_op_1529_, lean_object* v_snd_1530_, lean_object* v_val_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_fst_1534_, uint8_t v_a_1535_, lean_object* v_s_1536_){
_start:
{
lean_object* v_structs_1537_; lean_object* v_opIdOf_1538_; lean_object* v_exprToOpIds_1539_; lean_object* v_steps_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1554_; 
v_structs_1537_ = lean_ctor_get(v_s_1536_, 0);
v_opIdOf_1538_ = lean_ctor_get(v_s_1536_, 1);
v_exprToOpIds_1539_ = lean_ctor_get(v_s_1536_, 2);
v_steps_1540_ = lean_ctor_get(v_s_1536_, 3);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_s_1536_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1542_ = v_s_1536_;
v_isShared_1543_ = v_isSharedCheck_1554_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_steps_1540_);
lean_inc(v_exprToOpIds_1539_);
lean_inc(v_opIdOf_1538_);
lean_inc(v_structs_1537_);
lean_dec(v_s_1536_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1554_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
v___x_1547_ = lean_box(1);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1526_);
lean_ctor_set(v___x_1549_, 1, v_binderType_1527_);
lean_ctor_set(v___x_1549_, 2, v_a_1528_);
lean_ctor_set(v___x_1549_, 3, v_op_1529_);
lean_ctor_set(v___x_1549_, 4, v_snd_1530_);
lean_ctor_set(v___x_1549_, 5, v_val_1531_);
lean_ctor_set(v___x_1549_, 6, v_a_1532_);
lean_ctor_set(v___x_1549_, 7, v_a_1533_);
lean_ctor_set(v___x_1549_, 8, v_fst_1534_);
lean_ctor_set(v___x_1549_, 9, v___x_1544_);
lean_ctor_set(v___x_1549_, 10, v___x_1545_);
lean_ctor_set(v___x_1549_, 11, v___x_1546_);
lean_ctor_set(v___x_1549_, 12, v___x_1546_);
lean_ctor_set(v___x_1549_, 13, v___x_1545_);
lean_ctor_set(v___x_1549_, 14, v___x_1547_);
lean_ctor_set(v___x_1549_, 15, v___x_1548_);
lean_ctor_set(v___x_1549_, 16, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*17, v_a_1535_);
v___x_1550_ = lean_array_push(v_structs_1537_, v___x_1549_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1550_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_opIdOf_1538_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_exprToOpIds_1539_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_steps_1540_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* v___x_1555_, lean_object* v_binderType_1556_, lean_object* v_a_1557_, lean_object* v_op_1558_, lean_object* v_snd_1559_, lean_object* v_val_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_fst_1563_, lean_object* v_a_1564_, lean_object* v_s_1565_){
_start:
{
uint8_t v_a_158442__boxed_1566_; lean_object* v_res_1567_; 
v_a_158442__boxed_1566_ = lean_unbox(v_a_1564_);
v_res_1567_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1555_, v_binderType_1556_, v_a_1557_, v_op_1558_, v_snd_1559_, v_val_1560_, v_a_1561_, v_a_1562_, v_fst_1563_, v_a_158442__boxed_1566_, v_s_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* v_m_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_buckets_1570_; lean_object* v___x_1571_; uint64_t v___y_1573_; 
v_buckets_1570_ = lean_ctor_get(v_m_1568_, 1);
v___x_1571_ = lean_array_get_size(v_buckets_1570_);
if (lean_obj_tag(v_a_1569_) == 0)
{
uint64_t v___x_1587_; 
v___x_1587_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_1573_ = v___x_1587_;
goto v___jp_1572_;
}
else
{
uint64_t v_hash_1588_; 
v_hash_1588_ = lean_ctor_get_uint64(v_a_1569_, sizeof(void*)*2);
v___y_1573_ = v_hash_1588_;
goto v___jp_1572_;
}
v___jp_1572_:
{
uint64_t v___x_1574_; uint64_t v___x_1575_; uint64_t v_fold_1576_; uint64_t v___x_1577_; uint64_t v___x_1578_; uint64_t v___x_1579_; size_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1574_ = 32ULL;
v___x_1575_ = lean_uint64_shift_right(v___y_1573_, v___x_1574_);
v_fold_1576_ = lean_uint64_xor(v___y_1573_, v___x_1575_);
v___x_1577_ = 16ULL;
v___x_1578_ = lean_uint64_shift_right(v_fold_1576_, v___x_1577_);
v___x_1579_ = lean_uint64_xor(v_fold_1576_, v___x_1578_);
v___x_1580_ = lean_uint64_to_usize(v___x_1579_);
v___x_1581_ = lean_usize_of_nat(v___x_1571_);
v___x_1582_ = ((size_t)1ULL);
v___x_1583_ = lean_usize_sub(v___x_1581_, v___x_1582_);
v___x_1584_ = lean_usize_land(v___x_1580_, v___x_1583_);
v___x_1585_ = lean_array_uget_borrowed(v_buckets_1570_, v___x_1584_);
v___x_1586_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_1569_, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* v_m_1589_, lean_object* v_a_1590_){
_start:
{
uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_res_1591_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_m_1589_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1593_; double v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_float_of_nat(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* v_cls_1598_, lean_object* v_msg_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_ref_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1651_; 
v_ref_1605_ = lean_ctor_get(v___y_1602_, 5);
v___x_1606_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1651_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1651_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v_traceState_1612_; lean_object* v_env_1613_; lean_object* v_nextMacroScope_1614_; lean_object* v_ngen_1615_; lean_object* v_auxDeclNGen_1616_; lean_object* v_cache_1617_; lean_object* v_messages_1618_; lean_object* v_infoState_1619_; lean_object* v_snapshotTasks_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1650_; 
v___x_1611_ = lean_st_ref_take(v___y_1603_);
v_traceState_1612_ = lean_ctor_get(v___x_1611_, 4);
v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
v_nextMacroScope_1614_ = lean_ctor_get(v___x_1611_, 1);
v_ngen_1615_ = lean_ctor_get(v___x_1611_, 2);
v_auxDeclNGen_1616_ = lean_ctor_get(v___x_1611_, 3);
v_cache_1617_ = lean_ctor_get(v___x_1611_, 5);
v_messages_1618_ = lean_ctor_get(v___x_1611_, 6);
v_infoState_1619_ = lean_ctor_get(v___x_1611_, 7);
v_snapshotTasks_1620_ = lean_ctor_get(v___x_1611_, 8);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1650_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snapshotTasks_1620_);
lean_inc(v_infoState_1619_);
lean_inc(v_messages_1618_);
lean_inc(v_cache_1617_);
lean_inc(v_traceState_1612_);
lean_inc(v_auxDeclNGen_1616_);
lean_inc(v_ngen_1615_);
lean_inc(v_nextMacroScope_1614_);
lean_inc(v_env_1613_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1650_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
uint64_t v_tid_1624_; lean_object* v_traces_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1649_; 
v_tid_1624_ = lean_ctor_get_uint64(v_traceState_1612_, sizeof(void*)*1);
v_traces_1625_ = lean_ctor_get(v_traceState_1612_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_traceState_1612_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1627_ = v_traceState_1612_;
v_isShared_1628_ = v_isSharedCheck_1649_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_traces_1625_);
lean_dec(v_traceState_1612_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1649_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; double v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
v___x_1631_ = 0;
v___x_1632_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
v___x_1633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1633_, 0, v_cls_1598_);
lean_ctor_set(v___x_1633_, 1, v___x_1629_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
lean_ctor_set_float(v___x_1633_, sizeof(void*)*3, v___x_1630_);
lean_ctor_set_float(v___x_1633_, sizeof(void*)*3 + 8, v___x_1630_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*3 + 16, v___x_1631_);
v___x_1634_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2));
v___x_1635_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v_a_1607_);
lean_ctor_set(v___x_1635_, 2, v___x_1634_);
lean_inc(v_ref_1605_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_ref_1605_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_PersistentArray_push___redArg(v_traces_1625_, v___x_1636_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1637_);
v___x_1639_ = v___x_1627_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1637_);
lean_ctor_set_uint64(v_reuseFailAlloc_1648_, sizeof(void*)*1, v_tid_1624_);
v___x_1639_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v___x_1639_);
v___x_1641_ = v___x_1622_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_env_1613_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_nextMacroScope_1614_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_ngen_1615_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_auxDeclNGen_1616_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1647_, 5, v_cache_1617_);
lean_ctor_set(v_reuseFailAlloc_1647_, 6, v_messages_1618_);
lean_ctor_set(v_reuseFailAlloc_1647_, 7, v_infoState_1619_);
lean_ctor_set(v_reuseFailAlloc_1647_, 8, v_snapshotTasks_1620_);
v___x_1641_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_st_ref_set(v___y_1603_, v___x_1641_);
v___x_1643_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1643_);
v___x_1645_ = v___x_1609_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* v_cls_1652_, lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1652_, v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
v___x_1667_ = l_Lean_MessageData_ofFormat(v___x_1666_);
return v___x_1667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
return v___x_1670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15));
v___x_1687_ = l_Lean_Name_append(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* v_op_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___y_1721_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_fst_1830_; lean_object* v_snd_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v_f_1877_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; 
v_f_1877_ = l_Lean_Expr_getAppFn(v_op_1708_);
if (lean_obj_tag(v_f_1877_) == 4)
{
lean_object* v_declName_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_declName_2140_ = lean_ctor_get(v_f_1877_, 0);
lean_inc(v_declName_2140_);
v___x_2141_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_2141_, v_declName_2140_);
lean_dec(v_declName_2140_);
if (v___x_2142_ == 0)
{
v___y_1879_ = v_a_1709_;
v___y_1880_ = v_a_1710_;
v___y_1881_ = v_a_1711_;
v___y_1882_ = v_a_1712_;
v___y_1883_ = v_a_1713_;
v___y_1884_ = v_a_1714_;
v___y_1885_ = v_a_1715_;
v___y_1886_ = v_a_1716_;
v___y_1887_ = v_a_1717_;
v___y_1888_ = v_a_1718_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_2143_ = lean_box(0);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
return v___x_2144_;
}
}
else
{
v___y_1879_ = v_a_1709_;
v___y_1880_ = v_a_1710_;
v___y_1881_ = v_a_1711_;
v___y_1882_ = v_a_1712_;
v___y_1883_ = v_a_1713_;
v___y_1884_ = v_a_1714_;
v___y_1885_ = v_a_1715_;
v___y_1886_ = v_a_1716_;
v___y_1887_ = v_a_1717_;
v___y_1888_ = v_a_1718_;
goto v___jp_1878_;
}
v___jp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___y_1721_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
v___jp_1724_:
{
if (lean_obj_tag(v___y_1725_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v___y_1725_, 0);
lean_inc(v_val_1737_);
lean_dec_ref(v___y_1725_);
v___x_1738_ = l_Lean_Meta_Grind_AC_mkVar(v_val_1737_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref(v___x_1738_);
v___y_1721_ = v___y_1726_;
goto v___jp_1720_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v___y_1726_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_dec(v___y_1725_);
v___y_1721_ = v___y_1726_;
goto v___jp_1720_;
}
}
v___jp_1747_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___y_1749_);
lean_ctor_set(v___x_1763_, 1, v___y_1762_);
lean_inc(v___y_1756_);
v___x_1764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_1756_, v___x_1763_, v___y_1758_, v___y_1759_, v___y_1755_, v___y_1757_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_dec_ref(v___x_1764_);
v___y_1725_ = v___y_1752_;
v___y_1726_ = v___y_1760_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1750_;
v___y_1729_ = v___y_1753_;
v___y_1730_ = v___y_1754_;
v___y_1731_ = v___y_1761_;
v___y_1732_ = v___y_1751_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___y_1759_;
v___y_1735_ = v___y_1755_;
v___y_1736_ = v___y_1757_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v___y_1760_);
lean_dec(v___y_1752_);
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
v___jp_1773_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_inc_ref(v___y_1788_);
v___x_1789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___y_1788_);
v___x_1790_ = l_Lean_MessageData_ofFormat(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___y_1779_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
if (lean_obj_tag(v___y_1777_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___x_1793_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
v___y_1753_ = v___y_1778_;
v___y_1754_ = v___y_1780_;
v___y_1755_ = v___y_1781_;
v___y_1756_ = v___y_1782_;
v___y_1757_ = v___y_1783_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1785_;
v___y_1760_ = v___y_1786_;
v___y_1761_ = v___y_1787_;
v___y_1762_ = v___x_1794_;
goto v___jp_1747_;
}
else
{
lean_object* v_val_1795_; lean_object* v___x_1796_; 
v_val_1795_ = lean_ctor_get(v___y_1777_, 0);
lean_inc(v_val_1795_);
v___x_1796_ = l_Lean_MessageData_ofExpr(v_val_1795_);
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___x_1793_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
v___y_1753_ = v___y_1778_;
v___y_1754_ = v___y_1780_;
v___y_1755_ = v___y_1781_;
v___y_1756_ = v___y_1782_;
v___y_1757_ = v___y_1783_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1785_;
v___y_1760_ = v___y_1786_;
v___y_1761_ = v___y_1787_;
v___y_1762_ = v___x_1796_;
goto v___jp_1747_;
}
}
v___jp_1797_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc_ref(v___y_1813_);
v___x_1814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___y_1813_);
v___x_1815_ = l_Lean_MessageData_ofFormat(v___x_1814_);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1806_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
if (lean_obj_tag(v___y_1799_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___x_1818_;
v___y_1780_ = v___y_1804_;
v___y_1781_ = v___y_1805_;
v___y_1782_ = v___y_1807_;
v___y_1783_ = v___y_1808_;
v___y_1784_ = v___y_1809_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v___y_1811_;
v___y_1787_ = v___y_1812_;
v___y_1788_ = v___x_1819_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___y_1799_);
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___x_1818_;
v___y_1780_ = v___y_1804_;
v___y_1781_ = v___y_1805_;
v___y_1782_ = v___y_1807_;
v___y_1783_ = v___y_1808_;
v___y_1784_ = v___y_1809_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v___y_1811_;
v___y_1787_ = v___y_1812_;
v___y_1788_ = v___x_1820_;
goto v___jp_1773_;
}
}
v___jp_1821_:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_1832_, v___y_1840_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v_structs_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1842_);
v_structs_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc_ref(v_structs_1844_);
lean_dec(v_a_1843_);
v___x_1845_ = lean_array_get_size(v_structs_1844_);
lean_dec_ref(v_structs_1844_);
v___x_1846_ = lean_box(v___y_1827_);
lean_inc(v_snd_1831_);
lean_inc_ref(v_op_1708_);
v___f_1847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(v___f_1847_, 0, v___x_1845_);
lean_closure_set(v___f_1847_, 1, v___y_1826_);
lean_closure_set(v___f_1847_, 2, v___y_1823_);
lean_closure_set(v___f_1847_, 3, v_op_1708_);
lean_closure_set(v___f_1847_, 4, v_snd_1831_);
lean_closure_set(v___f_1847_, 5, v___y_1822_);
lean_closure_set(v___f_1847_, 6, v___y_1824_);
lean_closure_set(v___f_1847_, 7, v___y_1825_);
lean_closure_set(v___f_1847_, 8, v_fst_1830_);
lean_closure_set(v___f_1847_, 9, v___x_1846_);
v___x_1848_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1849_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1848_, v___f_1847_, v___y_1832_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_options_1850_; uint8_t v_hasTrace_1851_; 
lean_dec_ref(v___x_1849_);
v_options_1850_ = lean_ctor_get(v___y_1840_, 2);
v_hasTrace_1851_ = lean_ctor_get_uint8(v_options_1850_, sizeof(void*)*1);
if (v_hasTrace_1851_ == 0)
{
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v_op_1708_);
v___y_1725_ = v_snd_1831_;
v___y_1726_ = v___x_1845_;
v___y_1727_ = v___y_1832_;
v___y_1728_ = v___y_1833_;
v___y_1729_ = v___y_1834_;
v___y_1730_ = v___y_1835_;
v___y_1731_ = v___y_1836_;
v___y_1732_ = v___y_1837_;
v___y_1733_ = v___y_1838_;
v___y_1734_ = v___y_1839_;
v___y_1735_ = v___y_1840_;
v___y_1736_ = v___y_1841_;
goto v___jp_1724_;
}
else
{
lean_object* v_inheritedTraceOptions_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_inheritedTraceOptions_1852_ = lean_ctor_get(v___y_1840_, 13);
v___x_1853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
v___x_1855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1852_, v_options_1850_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v_op_1708_);
v___y_1725_ = v_snd_1831_;
v___y_1726_ = v___x_1845_;
v___y_1727_ = v___y_1832_;
v___y_1728_ = v___y_1833_;
v___y_1729_ = v___y_1834_;
v___y_1730_ = v___y_1835_;
v___y_1731_ = v___y_1836_;
v___y_1732_ = v___y_1837_;
v___y_1733_ = v___y_1838_;
v___y_1734_ = v___y_1839_;
v___y_1735_ = v___y_1840_;
v___y_1736_ = v___y_1841_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = l_Lean_MessageData_ofExpr(v_op_1708_);
v___x_1857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
if (lean_obj_tag(v___y_1829_) == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1798_ = v___y_1832_;
v___y_1799_ = v___y_1828_;
v___y_1800_ = v___y_1833_;
v___y_1801_ = v___y_1837_;
v___y_1802_ = v_snd_1831_;
v___y_1803_ = v___y_1834_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v___y_1840_;
v___y_1806_ = v___x_1858_;
v___y_1807_ = v___x_1853_;
v___y_1808_ = v___y_1841_;
v___y_1809_ = v___y_1838_;
v___y_1810_ = v___y_1839_;
v___y_1811_ = v___x_1845_;
v___y_1812_ = v___y_1836_;
v___y_1813_ = v___x_1859_;
goto v___jp_1797_;
}
else
{
lean_object* v___x_1860_; 
lean_dec_ref(v___y_1829_);
v___x_1860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1798_ = v___y_1832_;
v___y_1799_ = v___y_1828_;
v___y_1800_ = v___y_1833_;
v___y_1801_ = v___y_1837_;
v___y_1802_ = v_snd_1831_;
v___y_1803_ = v___y_1834_;
v___y_1804_ = v___y_1835_;
v___y_1805_ = v___y_1840_;
v___y_1806_ = v___x_1858_;
v___y_1807_ = v___x_1853_;
v___y_1808_ = v___y_1841_;
v___y_1809_ = v___y_1838_;
v___y_1810_ = v___y_1839_;
v___y_1811_ = v___x_1845_;
v___y_1812_ = v___y_1836_;
v___y_1813_ = v___x_1860_;
goto v___jp_1797_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_snd_1831_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v_op_1708_);
v_a_1861_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1849_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1849_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_snd_1831_);
lean_dec(v_fst_1830_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_op_1708_);
v_a_1869_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1842_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1842_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
v___jp_1878_:
{
lean_object* v___x_1889_; 
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc_ref(v_op_1708_);
v___x_1889_ = lean_infer_type(v_op_1708_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
v___x_1891_ = lean_whnf(v_a_1890_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_2123_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_2123_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_2123_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
if (lean_obj_tag(v_a_1892_) == 7)
{
lean_object* v_binderType_1896_; lean_object* v_body_1897_; uint8_t v___x_1898_; 
v_binderType_1896_ = lean_ctor_get(v_a_1892_, 1);
lean_inc_ref(v_binderType_1896_);
v_body_1897_ = lean_ctor_get(v_a_1892_, 2);
lean_inc_ref(v_body_1897_);
lean_dec_ref(v_a_1892_);
v___x_1898_ = l_Lean_Expr_hasLooseBVars(v_body_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_del_object(v___x_1894_);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
v___x_1899_ = lean_whnf(v_body_1897_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_2106_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_2106_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_2106_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
if (lean_obj_tag(v_a_1900_) == 7)
{
lean_object* v_binderType_1904_; lean_object* v_body_1905_; uint8_t v___x_1906_; 
v_binderType_1904_ = lean_ctor_get(v_a_1900_, 1);
lean_inc_ref(v_binderType_1904_);
v_body_1905_ = lean_ctor_get(v_a_1900_, 2);
lean_inc_ref(v_body_1905_);
lean_dec_ref(v_a_1900_);
v___x_1906_ = l_Lean_Expr_hasLooseBVars(v_body_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_del_object(v___x_1902_);
lean_inc_ref(v_binderType_1896_);
v___x_1907_ = l_Lean_Meta_isExprDefEq(v_binderType_1896_, v_binderType_1904_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_2089_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_2089_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_2089_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec_ref(v_body_1905_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_1913_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1913_);
v___x_1915_ = v___x_1910_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v___x_1917_; 
lean_del_object(v___x_1910_);
lean_inc_ref(v_binderType_1896_);
v___x_1917_ = l_Lean_Meta_isExprDefEq(v_binderType_1896_, v_body_1905_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2080_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_2080_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2080_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_1923_ = lean_box(0);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
lean_object* v___x_1927_; 
lean_del_object(v___x_1920_);
v___x_1927_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_1708_, v_f_1877_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec_ref(v_f_1877_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_2071_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_2071_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_2071_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_unbox(v_a_1928_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_del_object(v___x_1930_);
lean_inc_ref(v_binderType_1896_);
v___x_1933_ = l_Lean_Meta_getLevel(v_binderType_1896_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc_n(v_a_1934_, 2);
lean_dec_ref(v___x_1933_);
v___x_1935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21));
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_inc_ref(v___x_1937_);
v___x_1938_ = l_Lean_mkConst(v___x_1935_, v___x_1937_);
lean_inc_ref(v_op_1708_);
lean_inc_ref(v_binderType_1896_);
v___x_1939_ = l_Lean_mkAppB(v___x_1938_, v_binderType_1896_, v_op_1708_);
v___x_1940_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1939_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_2050_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_2050_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_2050_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
if (lean_obj_tag(v_a_1941_) == 1)
{
lean_object* v_val_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2045_; 
lean_del_object(v___x_1943_);
v_val_1945_ = lean_ctor_get(v_a_1941_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_1941_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_1947_ = v_a_1941_;
v_isShared_1948_ = v_isSharedCheck_2045_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_val_1945_);
lean_dec(v_a_1941_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2045_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23));
lean_inc_ref(v___x_1937_);
v___x_1950_ = l_Lean_mkConst(v___x_1949_, v___x_1937_);
lean_inc_ref(v_op_1708_);
lean_inc_ref(v_binderType_1896_);
v___x_1951_ = l_Lean_mkAppB(v___x_1950_, v_binderType_1896_, v_op_1708_);
v___x_1952_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1951_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25));
lean_inc_ref(v___x_1937_);
v___x_1955_ = l_Lean_mkConst(v___x_1954_, v___x_1937_);
lean_inc_ref(v_op_1708_);
lean_inc_ref(v_binderType_1896_);
v___x_1956_ = l_Lean_mkAppB(v___x_1955_, v_binderType_1896_, v_op_1708_);
v___x_1957_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1956_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
lean_inc_ref(v_binderType_1896_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v_binderType_1896_);
v___x_1960_ = v___x_1947_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_binderType_1896_);
v___x_1960_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = 0;
v___x_1962_ = lean_box(0);
v___x_1963_ = l_Lean_Meta_mkFreshExprMVar(v___x_1960_, v___x_1961_, v___x_1962_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc_n(v_a_1964_, 2);
lean_dec_ref(v___x_1963_);
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27));
v___x_1966_ = l_Lean_mkConst(v___x_1965_, v___x_1937_);
lean_inc_ref(v_op_1708_);
lean_inc_ref(v_binderType_1896_);
v___x_1967_ = l_Lean_mkApp3(v___x_1966_, v_binderType_1896_, v_op_1708_, v_a_1964_);
v___x_1968_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_1967_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
if (lean_obj_tag(v_a_1969_) == 1)
{
lean_object* v___x_1970_; lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2009_; 
v___x_1970_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_1964_, v___y_1886_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_2009_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2009_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_1971_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_1708_, v___y_1879_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v___x_1979_ = lean_box(0);
lean_inc(v___y_1888_);
lean_inc_ref(v___y_1887_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1885_);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc(v___y_1879_);
lean_inc(v_a_1976_);
v___x_1980_ = lean_grind_internalize(v_a_1976_, v_a_1978_, v___x_1979_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref(v___x_1980_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 1);
lean_ctor_set(v___x_1973_, 0, v_a_1976_);
v___x_1982_ = v___x_1973_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1976_);
v___x_1982_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
lean_inc(v_a_1953_);
lean_inc(v_a_1958_);
v___y_1822_ = v_val_1945_;
v___y_1823_ = v_a_1934_;
v___y_1824_ = v_a_1958_;
v___y_1825_ = v_a_1953_;
v___y_1826_ = v_binderType_1896_;
v___y_1827_ = v___x_1983_;
v___y_1828_ = v_a_1958_;
v___y_1829_ = v_a_1953_;
v_fst_1830_ = v_a_1969_;
v_snd_1831_ = v___x_1982_;
v___y_1832_ = v___y_1879_;
v___y_1833_ = v___y_1880_;
v___y_1834_ = v___y_1881_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___y_1883_;
v___y_1837_ = v___y_1884_;
v___y_1838_ = v___y_1885_;
v___y_1839_ = v___y_1886_;
v___y_1840_ = v___y_1887_;
v___y_1841_ = v___y_1888_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1958_);
lean_dec(v_a_1953_);
lean_dec(v_val_1945_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_1985_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1980_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1980_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_a_1976_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1958_);
lean_dec(v_a_1953_);
lean_dec(v_val_1945_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_1993_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1977_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1977_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1973_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1958_);
lean_dec(v_a_1953_);
lean_dec(v_val_1945_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2001_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1975_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1975_);
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
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
lean_dec(v_a_1969_);
lean_dec(v_a_1964_);
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
lean_inc(v_a_1953_);
lean_inc(v_a_1958_);
v___y_1822_ = v_val_1945_;
v___y_1823_ = v_a_1934_;
v___y_1824_ = v_a_1958_;
v___y_1825_ = v_a_1953_;
v___y_1826_ = v_binderType_1896_;
v___y_1827_ = v___x_2011_;
v___y_1828_ = v_a_1958_;
v___y_1829_ = v_a_1953_;
v_fst_1830_ = v___x_2010_;
v_snd_1831_ = v___x_2010_;
v___y_1832_ = v___y_1879_;
v___y_1833_ = v___y_1880_;
v___y_1834_ = v___y_1881_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___y_1883_;
v___y_1837_ = v___y_1884_;
v___y_1838_ = v___y_1885_;
v___y_1839_ = v___y_1886_;
v___y_1840_ = v___y_1887_;
v___y_1841_ = v___y_1888_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_a_1964_);
lean_dec(v_a_1958_);
lean_dec(v_a_1953_);
lean_dec(v_val_1945_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2012_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1968_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1968_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_a_1958_);
lean_dec(v_a_1953_);
lean_dec(v_val_1945_);
lean_dec_ref(v___x_1937_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2020_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1963_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1963_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_1953_);
lean_del_object(v___x_1947_);
lean_dec(v_val_1945_);
lean_dec_ref(v___x_1937_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2029_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1957_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1957_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_1947_);
lean_dec(v_val_1945_);
lean_dec_ref(v___x_1937_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2037_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1952_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1952_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v_a_1941_);
lean_dec_ref(v___x_1937_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v___x_2046_ = lean_box(0);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_2046_);
v___x_2048_ = v___x_1943_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v___x_1937_);
lean_dec(v_a_1934_);
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2051_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1940_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1940_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2059_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1933_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1933_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_dec(v_a_1928_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v___x_2067_ = lean_box(0);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_2067_);
v___x_2069_ = v___x_1930_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_op_1708_);
v_a_2072_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_1927_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_1927_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
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
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v_a_2081_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_1917_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_1917_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_body_1905_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v_a_2090_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_1907_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_1907_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
lean_dec_ref(v_body_1905_);
lean_dec_ref(v_binderType_1904_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_2098_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_2098_);
v___x_2100_ = v___x_1902_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec(v_a_1900_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_2102_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_2102_);
v___x_2104_ = v___x_1902_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v_a_2107_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_1899_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_1899_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec_ref(v_body_1897_);
lean_dec_ref(v_binderType_1896_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_2115_ = lean_box(0);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_2115_);
v___x_2117_ = v___x_1894_;
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
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec(v_a_1892_);
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v___x_2119_ = lean_box(0);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_2119_);
v___x_2121_ = v___x_1894_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v_a_2124_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_1891_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_1891_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_op_1708_);
v_a_2132_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_1889_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_1889_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* v_op_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec(v_a_2146_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* v_cls_2158_, lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_2158_, v_msg_2159_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* v_cls_2172_, lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2172_, v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
return v_res_2185_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* v_00_u03b2_2186_, lean_object* v_m_2187_, lean_object* v_a_2188_){
_start:
{
uint8_t v___x_2189_; 
v___x_2189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_2187_, v_a_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_m_2191_, lean_object* v_a_2192_){
_start:
{
uint8_t v_res_2193_; lean_object* v_r_2194_; 
v_res_2193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_2190_, v_m_2191_, v_a_2192_);
lean_dec(v_a_2192_);
lean_dec_ref(v_m_2191_);
v_r_2194_ = lean_box(v_res_2193_);
return v_r_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* v_op_2195_, lean_object* v_a_2196_, lean_object* v_s_2197_){
_start:
{
lean_object* v_structs_2198_; lean_object* v_opIdOf_2199_; lean_object* v_exprToOpIds_2200_; lean_object* v_steps_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2209_; 
v_structs_2198_ = lean_ctor_get(v_s_2197_, 0);
v_opIdOf_2199_ = lean_ctor_get(v_s_2197_, 1);
v_exprToOpIds_2200_ = lean_ctor_get(v_s_2197_, 2);
v_steps_2201_ = lean_ctor_get(v_s_2197_, 3);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_s_2197_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2203_ = v_s_2197_;
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_steps_2201_);
lean_inc(v_exprToOpIds_2200_);
lean_inc(v_opIdOf_2199_);
lean_inc(v_structs_2198_);
lean_dec(v_s_2197_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2209_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2205_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_2199_, v_op_2195_, v_a_2196_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v___x_2205_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_structs_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_exprToOpIds_2200_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_steps_2201_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* v_op_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2211_, v_a_2219_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2254_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2254_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2254_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_opIdOf_2227_; lean_object* v___x_2228_; 
v_opIdOf_2227_ = lean_ctor_get(v_a_2223_, 1);
lean_inc_ref(v_opIdOf_2227_);
lean_dec(v_a_2223_);
v___x_2228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_2227_, v_op_2210_);
lean_dec_ref(v_opIdOf_2227_);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v___x_2231_; 
lean_dec_ref(v_op_2210_);
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_val_2229_);
lean_dec_ref(v___x_2228_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_val_2229_);
v___x_2231_ = v___x_2225_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_val_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
lean_object* v___x_2233_; 
lean_dec(v___x_2228_);
lean_del_object(v___x_2225_);
lean_inc_ref(v_op_2210_);
v___x_2233_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___f_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_n(v_a_2234_, 2);
lean_dec_ref(v___x_2233_);
v___f_2235_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2235_, 0, v_op_2210_);
lean_closure_set(v___f_2235_, 1, v_a_2234_);
v___x_2236_ = l_Lean_Meta_Grind_AC_acExt;
v___x_2237_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2236_, v___f_2235_, v_a_2211_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2245_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_a_2234_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2234_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2234_);
v_a_2246_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2237_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2237_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
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
lean_dec_ref(v_op_2210_);
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_op_2210_);
v_a_2255_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2222_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2222_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* v_op_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec(v_a_2264_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* v_e_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
uint8_t v___y_2290_; uint8_t v___x_2321_; 
v___x_2321_ = l_Lean_Expr_isApp(v_e_2276_);
if (v___x_2321_ == 0)
{
v___y_2290_ = v___x_2321_;
goto v___jp_2289_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = l_Lean_Expr_appFn_x21(v_e_2276_);
v___x_2323_ = l_Lean_Expr_isApp(v___x_2322_);
lean_dec_ref(v___x_2322_);
v___y_2290_ = v___x_2323_;
goto v___jp_2289_;
}
v___jp_2289_:
{
if (v___y_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_Grind_AC_getOp(v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2312_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2312_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2312_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = l_Lean_Expr_appFn_x21(v_e_2276_);
v___x_2299_ = l_Lean_Expr_appFn_x21(v___x_2298_);
v___x_2300_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2299_, v_a_2294_);
lean_dec(v_a_2294_);
lean_dec_ref(v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_dec_ref(v___x_2298_);
v___x_2301_ = lean_box(0);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2301_);
v___x_2303_ = v___x_2296_;
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
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2305_ = l_Lean_Expr_appArg_x21(v___x_2298_);
lean_dec_ref(v___x_2298_);
v___x_2306_ = l_Lean_Expr_appArg_x21(v_e_2276_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2308_);
v___x_2310_ = v___x_2296_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2293_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2293_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* v_e_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_e_2324_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2366_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2366_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2366_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_commInst_x3f_2355_; 
v_commInst_x3f_2355_ = lean_ctor_get(v_a_2351_, 7);
lean_inc(v_commInst_x3f_2355_);
lean_dec(v_a_2351_);
if (lean_obj_tag(v_commInst_x3f_2355_) == 0)
{
uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = 0;
v___x_2357_ = lean_box(v___x_2356_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2357_);
v___x_2359_ = v___x_2353_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
else
{
uint8_t v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec_ref(v_commInst_x3f_2355_);
v___x_2361_ = 1;
v___x_2362_ = lean_box(v___x_2361_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2362_);
v___x_2364_ = v___x_2353_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2350_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2350_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec(v_a_2375_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2416_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2416_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2416_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_neutralInst_x3f_2405_; 
v_neutralInst_x3f_2405_ = lean_ctor_get(v_a_2401_, 8);
lean_inc(v_neutralInst_x3f_2405_);
lean_dec(v_a_2401_);
if (lean_obj_tag(v_neutralInst_x3f_2405_) == 0)
{
uint8_t v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = 0;
v___x_2407_ = lean_box(v___x_2406_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2407_);
v___x_2409_ = v___x_2403_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
else
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_dec_ref(v_neutralInst_x3f_2405_);
v___x_2411_ = 1;
v___x_2412_ = lean_box(v___x_2411_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2412_);
v___x_2414_ = v___x_2403_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2400_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2400_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec(v_a_2425_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2466_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2466_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2466_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_idempotentInst_x3f_2455_; 
v_idempotentInst_x3f_2455_ = lean_ctor_get(v_a_2451_, 6);
lean_inc(v_idempotentInst_x3f_2455_);
lean_dec(v_a_2451_);
if (lean_obj_tag(v_idempotentInst_x3f_2455_) == 0)
{
uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2456_ = 0;
v___x_2457_ = lean_box(v___x_2456_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2457_);
v___x_2459_ = v___x_2453_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
else
{
uint8_t v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec_ref(v_idempotentInst_x3f_2455_);
v___x_2461_ = 1;
v___x_2462_ = lean_box(v___x_2461_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2462_);
v___x_2464_ = v___x_2453_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2450_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2450_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec(v_a_2475_);
return v_res_2487_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
