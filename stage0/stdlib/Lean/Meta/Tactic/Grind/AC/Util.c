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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = l_Lean_Meta_Grind_AC_acExt;
v___x_5_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_4_, v_a_1_, v_a_2_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_get_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_6_;
v_res_6_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1_, v_a_2_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_7_, v_a_8_);
lean_dec_ref(v_a_8_);
lean_dec(v_a_7_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Grind_AC_get_x27(lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_11_, v_a_19_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_11_ = stack[0].m_obj;
lean_object* v_a_12_ = stack[1].m_obj;
lean_object* v_a_13_ = stack[2].m_obj;
lean_object* v_a_14_ = stack[3].m_obj;
lean_object* v_a_15_ = stack[4].m_obj;
lean_object* v_a_16_ = stack[5].m_obj;
lean_object* v_a_17_ = stack[6].m_obj;
lean_object* v_a_18_ = stack[7].m_obj;
lean_object* v_a_19_ = stack[8].m_obj;
lean_object* v_a_20_ = stack[9].m_obj;
lean_object* v_res_23_;
v_res_23_ = l_Lean_Meta_Grind_AC_get_x27(v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_get_x27___boxed(lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_Grind_AC_get_x27(v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec(v_a_24_);
return v_res_35_;
}
}
lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg(lean_object* v_f_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_Lean_Meta_Grind_AC_acExt;
v___x_40_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_39_, v_f_36_, v_a_37_);
return v___x_40_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_modify_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_36_ = stack[0].m_obj;
lean_object* v_a_37_ = stack[1].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_Meta_Grind_AC_modify_x27___redArg(v_f_36_, v_a_37_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(lean_object* v_f_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Meta_Grind_AC_modify_x27___redArg(v_f_42_, v_a_43_);
lean_dec(v_a_43_);
return v_res_45_;
}
}
lean_object* l_Lean_Meta_Grind_AC_modify_x27(lean_object* v_f_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l_Lean_Meta_Grind_AC_acExt;
v___x_59_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_58_, v_f_46_, v_a_47_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_modify_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_46_ = stack[0].m_obj;
lean_object* v_a_47_ = stack[1].m_obj;
lean_object* v_a_48_ = stack[2].m_obj;
lean_object* v_a_49_ = stack[3].m_obj;
lean_object* v_a_50_ = stack[4].m_obj;
lean_object* v_a_51_ = stack[5].m_obj;
lean_object* v_a_52_ = stack[6].m_obj;
lean_object* v_a_53_ = stack[7].m_obj;
lean_object* v_a_54_ = stack[8].m_obj;
lean_object* v_a_55_ = stack[9].m_obj;
lean_object* v_a_56_ = stack[10].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_Meta_Grind_AC_modify_x27(v_f_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modify_x27___boxed(lean_object* v_f_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Grind_AC_modify_x27(v_f_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
lean_dec(v_a_63_);
lean_dec(v_a_62_);
return v_res_73_;
}
}
lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_74_, v_a_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_75_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_92_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_92_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_92_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_92_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_acSteps_85_; lean_object* v_steps_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v_acSteps_85_ = lean_ctor_get(v_a_81_, 9);
lean_inc(v_acSteps_85_);
lean_dec(v_a_81_);
v_steps_86_ = lean_ctor_get(v_a_79_, 3);
lean_inc(v_steps_86_);
lean_dec(v_a_79_);
v___x_87_ = lean_nat_dec_le(v_acSteps_85_, v_steps_86_);
lean_dec(v_steps_86_);
lean_dec(v_acSteps_85_);
v___x_88_ = lean_box(v___x_87_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_88_);
v___x_90_ = v___x_83_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec(v_a_79_);
v_a_93_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_80_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_80_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_78_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_78_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_checkMaxSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_74_ = stack[0].m_obj;
lean_object* v_a_75_ = stack[1].m_obj;
lean_object* v_a_76_ = stack[2].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_74_, v_a_75_, v_a_76_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_110_, v_a_111_, v_a_112_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
return v_res_114_;
}
}
lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps(lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_115_, v_a_117_, v_a_123_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_checkMaxSteps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_115_ = stack[0].m_obj;
lean_object* v_a_116_ = stack[1].m_obj;
lean_object* v_a_117_ = stack[2].m_obj;
lean_object* v_a_118_ = stack[3].m_obj;
lean_object* v_a_119_ = stack[4].m_obj;
lean_object* v_a_120_ = stack[5].m_obj;
lean_object* v_a_121_ = stack[6].m_obj;
lean_object* v_a_122_ = stack[7].m_obj;
lean_object* v_a_123_ = stack[8].m_obj;
lean_object* v_a_124_ = stack[9].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Meta_Grind_AC_checkMaxSteps(v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_Grind_AC_checkMaxSteps(v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec(v_a_128_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(lean_object* v_s_140_){
_start:
{
lean_object* v_structs_141_; lean_object* v_opIdOf_142_; lean_object* v_exprToOpIds_143_; lean_object* v_steps_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_structs_141_ = lean_ctor_get(v_s_140_, 0);
v_opIdOf_142_ = lean_ctor_get(v_s_140_, 1);
v_exprToOpIds_143_ = lean_ctor_get(v_s_140_, 2);
v_steps_144_ = lean_ctor_get(v_s_140_, 3);
v_isSharedCheck_153_ = !lean_is_exclusive(v_s_140_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v_s_140_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_steps_144_);
lean_inc(v_exprToOpIds_143_);
lean_inc(v_opIdOf_142_);
lean_inc(v_structs_141_);
lean_dec(v_s_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_steps_144_, v___x_148_);
lean_dec(v_steps_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 3, v___x_149_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_structs_141_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_opIdOf_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_exprToOpIds_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg(lean_object* v_a_155_){
_start:
{
lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___f_157_ = ((lean_object*)(l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0));
v___x_158_ = l_Lean_Meta_Grind_AC_acExt;
v___x_159_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_158_, v___f_157_, v_a_155_);
return v___x_159_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_incSteps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_155_ = stack[0].m_obj;
lean_object* v_res_160_;
v_res_160_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_155_);
stack->m_obj
 = v_res_160_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_161_);
lean_dec(v_a_161_);
return v_res_163_;
}
}
lean_object* l_Lean_Meta_Grind_AC_incSteps(lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_164_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_incSteps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_164_ = stack[0].m_obj;
lean_object* v_a_165_ = stack[1].m_obj;
lean_object* v_a_166_ = stack[2].m_obj;
lean_object* v_a_167_ = stack[3].m_obj;
lean_object* v_a_168_ = stack[4].m_obj;
lean_object* v_a_169_ = stack[5].m_obj;
lean_object* v_a_170_ = stack[6].m_obj;
lean_object* v_a_171_ = stack[7].m_obj;
lean_object* v_a_172_ = stack[8].m_obj;
lean_object* v_a_173_ = stack[9].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Meta_Grind_AC_incSteps(v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_incSteps___boxed(lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Grind_AC_incSteps(v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec(v_a_177_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(lean_object* v_inst_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_apply_2(v_inst_189_, lean_box(0), v_inst_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(lean_object* v_m_192_, lean_object* v_n_193_, lean_object* v_inst_194_, lean_object* v_inst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_apply_2(v_inst_194_, lean_box(0), v_inst_195_);
return v___x_196_;
}
}
lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg(lean_object* v_opId_197_, lean_object* v_x_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc_ref(v_a_205_);
lean_inc(v_a_204_);
lean_inc_ref(v_a_203_);
lean_inc(v_a_202_);
lean_inc_ref(v_a_201_);
lean_inc(v_a_200_);
lean_inc(v_a_199_);
v___x_210_ = lean_apply_12(v_x_198_, v_opId_197_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, lean_box(0));
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_ACM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opId_197_ = stack[0].m_obj;
lean_object* v_x_198_ = stack[1].m_obj;
lean_object* v_a_199_ = stack[2].m_obj;
lean_object* v_a_200_ = stack[3].m_obj;
lean_object* v_a_201_ = stack[4].m_obj;
lean_object* v_a_202_ = stack[5].m_obj;
lean_object* v_a_203_ = stack[6].m_obj;
lean_object* v_a_204_ = stack[7].m_obj;
lean_object* v_a_205_ = stack[8].m_obj;
lean_object* v_a_206_ = stack[9].m_obj;
lean_object* v_a_207_ = stack[10].m_obj;
lean_object* v_a_208_ = stack[11].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Lean_Meta_Grind_AC_ACM_run___redArg(v_opId_197_, v_x_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(lean_object* v_opId_212_, lean_object* v_x_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Grind_AC_ACM_run___redArg(v_opId_212_, v_x_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
return v_res_225_;
}
}
lean_object* l_Lean_Meta_Grind_AC_ACM_run(lean_object* v_00_u03b1_226_, lean_object* v_opId_227_, lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
lean_inc(v_a_238_);
lean_inc_ref(v_a_237_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc(v_a_234_);
lean_inc_ref(v_a_233_);
lean_inc(v_a_232_);
lean_inc_ref(v_a_231_);
lean_inc(v_a_230_);
lean_inc(v_a_229_);
v___x_240_ = lean_apply_12(v_x_228_, v_opId_227_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, lean_box(0));
return v___x_240_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_ACM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_opId_227_ = stack[1].m_obj;
lean_object* v_x_228_ = stack[2].m_obj;
lean_object* v_a_229_ = stack[3].m_obj;
lean_object* v_a_230_ = stack[4].m_obj;
lean_object* v_a_231_ = stack[5].m_obj;
lean_object* v_a_232_ = stack[6].m_obj;
lean_object* v_a_233_ = stack[7].m_obj;
lean_object* v_a_234_ = stack[8].m_obj;
lean_object* v_a_235_ = stack[9].m_obj;
lean_object* v_a_236_ = stack[10].m_obj;
lean_object* v_a_237_ = stack[11].m_obj;
lean_object* v_a_238_ = stack[12].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_Meta_Grind_AC_ACM_run(lean_box(0), v_opId_227_, v_x_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_run___boxed(lean_object* v_00_u03b1_242_, lean_object* v_opId_243_, lean_object* v_x_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Grind_AC_ACM_run(v_00_u03b1_242_, v_opId_243_, v_x_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec(v_a_245_);
return v_res_256_;
}
}
lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg(lean_object* v_a_257_){
_start:
{
lean_object* v___x_259_; 
lean_inc(v_a_257_);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v_a_257_);
return v___x_259_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getOpId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_257_ = stack[0].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_Meta_Grind_AC_getOpId___redArg(v_a_257_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_AC_getOpId___redArg(v_a_261_);
lean_dec(v_a_261_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_Grind_AC_getOpId(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
lean_inc(v_a_264_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_a_264_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getOpId_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_264_ = stack[0].m_obj;
lean_object* v_a_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_a_270_ = stack[6].m_obj;
lean_object* v_a_271_ = stack[7].m_obj;
lean_object* v_a_272_ = stack[8].m_obj;
lean_object* v_a_273_ = stack[9].m_obj;
lean_object* v_a_274_ = stack[10].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Meta_Grind_AC_getOpId(v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId___boxed(lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_AC_getOpId(v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
lean_dec(v_a_278_);
return v_res_290_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(lean_object* v_msgData_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_env_298_; uint8_t v___x_299_; lean_object* v_env_300_; lean_object* v___x_301_; lean_object* v_toCold_302_; lean_object* v_mctx_303_; lean_object* v_lctx_304_; lean_object* v_options_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_env_298_);
lean_dec(v___x_297_);
v___x_299_ = 0;
v_env_300_ = l_Lean_Environment_setRecordingDeps(v_env_298_, v___x_299_);
v___x_301_ = lean_st_ref_get(v___y_293_);
v_toCold_302_ = lean_ctor_get(v___y_294_, 0);
v_mctx_303_ = lean_ctor_get(v___x_301_, 0);
lean_inc_ref(v_mctx_303_);
lean_dec(v___x_301_);
v_lctx_304_ = lean_ctor_get(v___y_292_, 2);
v_options_305_ = lean_ctor_get(v_toCold_302_, 2);
lean_inc_ref(v_options_305_);
lean_inc_ref(v_lctx_304_);
v___x_306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_306_, 0, v_env_300_);
lean_ctor_set(v___x_306_, 1, v_mctx_303_);
lean_ctor_set(v___x_306_, 2, v_lctx_304_);
lean_ctor_set(v___x_306_, 3, v_options_305_);
v___x_307_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v_msgData_291_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_291_ = stack[0].m_obj;
lean_object* v___y_292_ = stack[1].m_obj;
lean_object* v___y_293_ = stack[2].m_obj;
lean_object* v___y_294_ = stack[3].m_obj;
lean_object* v___y_295_ = stack[4].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(lean_object* v_msgData_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_ref_323_ = lean_ctor_get(v___y_320_, 2);
v___x_324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
lean_inc(v_ref_323_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_ref_323_);
lean_ctor_set(v___x_329_, 1, v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 1);
lean_ctor_set(v___x_327_, 0, v___x_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_317_ = stack[0].m_obj;
lean_object* v___y_318_ = stack[1].m_obj;
lean_object* v___y_319_ = stack[2].m_obj;
lean_object* v___y_320_ = stack[3].m_obj;
lean_object* v___y_321_ = stack[4].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct(lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_346_, v_a_354_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_371_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_371_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_371_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_371_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_structs_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_structs_362_ = lean_ctor_get(v_a_358_, 0);
lean_inc_ref(v_structs_362_);
lean_dec(v_a_358_);
v___x_363_ = lean_array_get_size(v_structs_362_);
v___x_364_ = lean_nat_dec_lt(v_a_345_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v_structs_362_);
lean_del_object(v___x_360_);
v___x_365_ = lean_obj_once(&l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1, &l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once, _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1);
v___x_366_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v___x_365_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_array_fget(v_structs_362_, v_a_345_);
lean_dec_ref(v_structs_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_367_);
v___x_369_ = v___x_360_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_357_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_357_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_ACM_getStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_345_ = stack[0].m_obj;
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_a_347_ = stack[2].m_obj;
lean_object* v_a_348_ = stack[3].m_obj;
lean_object* v_a_349_ = stack[4].m_obj;
lean_object* v_a_350_ = stack[5].m_obj;
lean_object* v_a_351_ = stack[6].m_obj;
lean_object* v_a_352_ = stack[7].m_obj;
lean_object* v_a_353_ = stack[8].m_obj;
lean_object* v_a_354_ = stack[9].m_obj;
lean_object* v_a_355_ = stack[10].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_393_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_object* v_00_u03b1_394_, lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v_msg_395_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_395_ = stack[1].m_obj;
lean_object* v___y_396_ = stack[2].m_obj;
lean_object* v___y_397_ = stack[3].m_obj;
lean_object* v___y_398_ = stack[4].m_obj;
lean_object* v___y_399_ = stack[5].m_obj;
lean_object* v___y_400_ = stack[6].m_obj;
lean_object* v___y_401_ = stack[7].m_obj;
lean_object* v___y_402_ = stack[8].m_obj;
lean_object* v___y_403_ = stack[9].m_obj;
lean_object* v___y_404_ = stack[10].m_obj;
lean_object* v___y_405_ = stack[11].m_obj;
lean_object* v___y_406_ = stack[12].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(lean_box(0), v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec(v___y_413_);
lean_dec(v___y_412_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(lean_object* v_a_426_, lean_object* v_f_427_, lean_object* v_s_428_){
_start:
{
lean_object* v_structs_429_; lean_object* v_opIdOf_430_; lean_object* v_exprToOpIds_431_; lean_object* v_steps_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_structs_429_ = lean_ctor_get(v_s_428_, 0);
v_opIdOf_430_ = lean_ctor_get(v_s_428_, 1);
v_exprToOpIds_431_ = lean_ctor_get(v_s_428_, 2);
v_steps_432_ = lean_ctor_get(v_s_428_, 3);
v___x_433_ = lean_array_get_size(v_structs_429_);
v___x_434_ = lean_nat_dec_lt(v_a_426_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec_ref(v_f_427_);
return v_s_428_;
}
else
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_446_; 
lean_inc(v_steps_432_);
lean_inc_ref(v_exprToOpIds_431_);
lean_inc_ref(v_opIdOf_430_);
lean_inc_ref(v_structs_429_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_s_428_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_447_ = lean_ctor_get(v_s_428_, 3);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_s_428_, 2);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_s_428_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_s_428_, 0);
lean_dec(v_unused_450_);
v___x_436_ = v_s_428_;
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_s_428_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_v_438_; lean_object* v___x_439_; lean_object* v_xs_x27_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_v_438_ = lean_array_fget(v_structs_429_, v_a_426_);
v___x_439_ = lean_box(0);
v_xs_x27_440_ = lean_array_fset(v_structs_429_, v_a_426_, v___x_439_);
v___x_441_ = lean_apply_1(v_f_427_, v_v_438_);
v___x_442_ = lean_array_fset(v_xs_x27_440_, v_a_426_, v___x_441_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_442_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_opIdOf_430_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_exprToOpIds_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_steps_432_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(lean_object* v_a_451_, lean_object* v_f_452_, lean_object* v_s_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(v_a_451_, v_f_452_, v_s_453_);
lean_dec(v_a_451_);
return v_res_454_;
}
}
lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg(lean_object* v_f_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_a_456_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_459_, 0, v_a_456_);
lean_closure_set(v___f_459_, 1, v_f_455_);
v___x_460_ = l_Lean_Meta_Grind_AC_acExt;
v___x_461_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_460_, v___f_459_, v_a_457_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_modifyStruct___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_455_ = stack[0].m_obj;
lean_object* v_a_456_ = stack[1].m_obj;
lean_object* v_a_457_ = stack[2].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_455_, v_a_456_, v_a_457_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(lean_object* v_f_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
return v_res_467_;
}
}
lean_object* l_Lean_Meta_Grind_AC_modifyStruct(lean_object* v_f_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_468_, v_a_469_, v_a_470_);
return v___x_481_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_modifyStruct_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_468_ = stack[0].m_obj;
lean_object* v_a_469_ = stack[1].m_obj;
lean_object* v_a_470_ = stack[2].m_obj;
lean_object* v_a_471_ = stack[3].m_obj;
lean_object* v_a_472_ = stack[4].m_obj;
lean_object* v_a_473_ = stack[5].m_obj;
lean_object* v_a_474_ = stack[6].m_obj;
lean_object* v_a_475_ = stack[7].m_obj;
lean_object* v_a_476_ = stack[8].m_obj;
lean_object* v_a_477_ = stack[9].m_obj;
lean_object* v_a_478_ = stack[10].m_obj;
lean_object* v_a_479_ = stack[11].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_Meta_Grind_AC_modifyStruct(v_f_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_modifyStruct___boxed(lean_object* v_f_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_Grind_AC_modifyStruct(v_f_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
lean_dec(v_a_484_);
return v_res_496_;
}
}
lean_object* l_Lean_Meta_Grind_AC_getOp(lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_op_514_; lean_object* v___x_516_; 
v_op_514_ = lean_ctor_get(v_a_510_, 3);
lean_inc_ref(v_op_514_);
lean_dec(v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_op_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_op_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_509_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_509_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_497_ = stack[0].m_obj;
lean_object* v_a_498_ = stack[1].m_obj;
lean_object* v_a_499_ = stack[2].m_obj;
lean_object* v_a_500_ = stack[3].m_obj;
lean_object* v_a_501_ = stack[4].m_obj;
lean_object* v_a_502_ = stack[5].m_obj;
lean_object* v_a_503_ = stack[6].m_obj;
lean_object* v_a_504_ = stack[7].m_obj;
lean_object* v_a_505_ = stack[8].m_obj;
lean_object* v_a_506_ = stack[9].m_obj;
lean_object* v_a_507_ = stack[10].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_Meta_Grind_AC_getOp(v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOp___boxed(lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Grind_AC_getOp(v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_542_) == 0)
{
return v_x_541_;
}
else
{
lean_object* v_key_543_; lean_object* v_value_544_; lean_object* v_tail_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_571_; 
v_key_543_ = lean_ctor_get(v_x_542_, 0);
v_value_544_ = lean_ctor_get(v_x_542_, 1);
v_tail_545_ = lean_ctor_get(v_x_542_, 2);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_542_);
if (v_isSharedCheck_571_ == 0)
{
v___x_547_ = v_x_542_;
v_isShared_548_ = v_isSharedCheck_571_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_tail_545_);
lean_inc(v_value_544_);
lean_inc(v_key_543_);
lean_dec(v_x_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_571_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint64_t v___y_551_; 
v___x_549_ = lean_array_get_size(v_x_541_);
if (lean_obj_tag(v_key_543_) == 0)
{
uint64_t v___x_569_; 
v___x_569_ = 1723ULL;
v___y_551_ = v___x_569_;
goto v___jp_550_;
}
else
{
uint64_t v_hash_570_; 
v_hash_570_ = lean_ctor_get_uint64(v_key_543_, sizeof(void*)*2);
v___y_551_ = v_hash_570_;
goto v___jp_550_;
}
v___jp_550_:
{
uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v_fold_554_; uint64_t v___x_555_; uint64_t v___x_556_; uint64_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_552_ = 32ULL;
v___x_553_ = lean_uint64_shift_right(v___y_551_, v___x_552_);
v_fold_554_ = lean_uint64_xor(v___y_551_, v___x_553_);
v___x_555_ = 16ULL;
v___x_556_ = lean_uint64_shift_right(v_fold_554_, v___x_555_);
v___x_557_ = lean_uint64_xor(v_fold_554_, v___x_556_);
v___x_558_ = lean_uint64_to_usize(v___x_557_);
v___x_559_ = lean_usize_of_nat(v___x_549_);
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_sub(v___x_559_, v___x_560_);
v___x_562_ = lean_usize_land(v___x_558_, v___x_561_);
v___x_563_ = lean_array_uget_borrowed(v_x_541_, v___x_562_);
lean_inc(v___x_563_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 2, v___x_563_);
v___x_565_ = v___x_547_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_key_543_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_value_544_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v___x_563_);
v___x_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_array_uset(v_x_541_, v___x_562_, v___x_565_);
v_x_541_ = v___x_566_;
v_x_542_ = v_tail_545_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_572_, lean_object* v_source_573_, lean_object* v_target_574_){
_start:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_get_size(v_source_573_);
v___x_576_ = lean_nat_dec_lt(v_i_572_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_source_573_);
lean_dec(v_i_572_);
return v_target_574_;
}
else
{
lean_object* v_es_577_; lean_object* v___x_578_; lean_object* v_source_579_; lean_object* v_target_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_es_577_ = lean_array_fget(v_source_573_, v_i_572_);
v___x_578_ = lean_box(0);
v_source_579_ = lean_array_fset(v_source_573_, v_i_572_, v___x_578_);
v_target_580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_574_, v_es_577_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_i_572_, v___x_581_);
lean_dec(v_i_572_);
v_i_572_ = v___x_582_;
v_source_573_ = v_source_579_;
v_target_574_ = v_target_580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object* v_data_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_nbuckets_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_585_ = lean_array_get_size(v_data_584_);
v___x_586_ = lean_unsigned_to_nat(2u);
v_nbuckets_587_ = lean_nat_mul(v___x_585_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_box(0);
v___x_590_ = lean_mk_array(v_nbuckets_587_, v___x_589_);
v___x_591_ = lean_array_propagate_mark(v_data_584_, v___x_590_);
v___x_592_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_588_, v_data_584_, v___x_591_);
return v___x_592_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
else
{
lean_object* v_key_596_; lean_object* v_tail_597_; uint8_t v___x_598_; 
v_key_596_ = lean_ctor_get(v_x_594_, 0);
v_tail_597_ = lean_ctor_get(v_x_594_, 2);
v___x_598_ = lean_name_eq(v_key_596_, v_a_593_);
if (v___x_598_ == 0)
{
v_x_594_ = v_tail_597_;
goto _start;
}
else
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_593_ = stack[0].m_obj;
lean_object* v_x_594_ = stack[1].m_obj;
uint8_t v_res_600_;
v_res_600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_593_, v_x_594_);
stack->m_num = v_res_600_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_601_, v_x_602_);
lean_dec(v_x_602_);
lean_dec(v_a_601_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object* v_m_605_, lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v_size_608_; lean_object* v_buckets_609_; lean_object* v___x_610_; uint64_t v___y_612_; 
v_size_608_ = lean_ctor_get(v_m_605_, 0);
v_buckets_609_ = lean_ctor_get(v_m_605_, 1);
v___x_610_ = lean_array_get_size(v_buckets_609_);
if (lean_obj_tag(v_a_606_) == 0)
{
uint64_t v___x_649_; 
v___x_649_ = 1723ULL;
v___y_612_ = v___x_649_;
goto v___jp_611_;
}
else
{
uint64_t v_hash_650_; 
v_hash_650_ = lean_ctor_get_uint64(v_a_606_, sizeof(void*)*2);
v___y_612_ = v_hash_650_;
goto v___jp_611_;
}
v___jp_611_:
{
uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v_fold_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v_bkt_624_; uint8_t v___x_625_; 
v___x_613_ = 32ULL;
v___x_614_ = lean_uint64_shift_right(v___y_612_, v___x_613_);
v_fold_615_ = lean_uint64_xor(v___y_612_, v___x_614_);
v___x_616_ = 16ULL;
v___x_617_ = lean_uint64_shift_right(v_fold_615_, v___x_616_);
v___x_618_ = lean_uint64_xor(v_fold_615_, v___x_617_);
v___x_619_ = lean_uint64_to_usize(v___x_618_);
v___x_620_ = lean_usize_of_nat(v___x_610_);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_sub(v___x_620_, v___x_621_);
v___x_623_ = lean_usize_land(v___x_619_, v___x_622_);
v_bkt_624_ = lean_array_uget_borrowed(v_buckets_609_, v___x_623_);
v___x_625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_606_, v_bkt_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_646_; 
lean_inc_ref(v_buckets_609_);
lean_inc(v_size_608_);
v_isSharedCheck_646_ = !lean_is_exclusive(v_m_605_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_647_ = lean_ctor_get(v_m_605_, 1);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_m_605_, 0);
lean_dec(v_unused_648_);
v___x_627_ = v_m_605_;
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
else
{
lean_dec(v_m_605_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_646_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v_size_x27_630_; lean_object* v___x_631_; lean_object* v_buckets_x27_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v_size_x27_630_ = lean_nat_add(v_size_608_, v___x_629_);
lean_dec(v_size_608_);
lean_inc(v_bkt_624_);
v___x_631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_631_, 0, v_a_606_);
lean_ctor_set(v___x_631_, 1, v_b_607_);
lean_ctor_set(v___x_631_, 2, v_bkt_624_);
v_buckets_x27_632_ = lean_array_uset(v_buckets_609_, v___x_623_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(4u);
v___x_634_ = lean_nat_mul(v_size_x27_630_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(3u);
v___x_636_ = lean_nat_div(v___x_634_, v___x_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_array_get_size(v_buckets_x27_632_);
v___x_638_ = lean_nat_dec_le(v___x_636_, v___x_637_);
lean_dec(v___x_636_);
if (v___x_638_ == 0)
{
lean_object* v_val_639_; lean_object* v___x_641_; 
v_val_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_buckets_x27_632_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_val_639_);
lean_ctor_set(v___x_627_, 0, v_size_x27_630_);
v___x_641_ = v___x_627_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_size_x27_630_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_val_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
else
{
lean_object* v___x_644_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_buckets_x27_632_);
lean_ctor_set(v___x_627_, 0, v_size_x27_630_);
v___x_644_ = v___x_627_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_size_x27_630_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_buckets_x27_632_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_dec(v_b_607_);
lean_dec(v_a_606_);
return v_m_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object* v_as_x27_651_, lean_object* v_b_652_){
_start:
{
if (lean_obj_tag(v_as_x27_651_) == 0)
{
return v_b_652_;
}
else
{
lean_object* v_head_653_; lean_object* v_tail_654_; lean_object* v___x_655_; lean_object* v_r_656_; 
v_head_653_ = lean_ctor_get(v_as_x27_651_, 0);
v_tail_654_ = lean_ctor_get(v_as_x27_651_, 1);
v___x_655_ = lean_box(0);
lean_inc(v_head_653_);
v_r_656_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_652_, v_head_653_, v___x_655_);
v_as_x27_651_ = v_tail_654_;
v_b_652_ = v_r_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_658_, lean_object* v_b_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_658_, v_b_659_);
lean_dec(v_as_x27_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object* v_m_661_, lean_object* v_l_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_l_662_, v_m_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(lean_object* v_m_664_, lean_object* v_l_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_664_, v_l_665_);
lean_dec(v_l_665_);
return v_res_666_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_box(0);
v___x_742_ = lean_unsigned_to_nat(16u);
v___x_743_ = lean_mk_array(v___x_742_, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36));
v___x_749_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_b_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_752_, v_a_753_, v_b_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object* v_as_756_, lean_object* v_as_x27_757_, lean_object* v_b_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_757_, v_b_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object* v_as_761_, lean_object* v_as_x27_762_, lean_object* v_b_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_as_761_, v_as_x27_762_, v_b_763_, v_a_764_);
lean_dec(v_as_x27_762_);
lean_dec(v_as_761_);
return v_res_765_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_766_, lean_object* v_a_767_, lean_object* v_x_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_767_ = stack[1].m_obj;
lean_object* v_x_768_ = stack[2].m_obj;
uint8_t v_res_770_;
v_res_770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_box(0), v_a_767_, v_x_768_);
stack->m_num = v_res_770_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_771_, lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_res_774_; lean_object* v_r_775_; 
v_res_774_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_771_, v_a_772_, v_x_773_);
lean_dec(v_x_773_);
lean_dec(v_a_772_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_776_, lean_object* v_data_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_data_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_779_, lean_object* v_i_780_, lean_object* v_source_781_, lean_object* v_target_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v_i_780_, v_source_781_, v_target_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_785_, v_x_786_);
return v___x_787_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(lean_object* v_op_813_, lean_object* v_f_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_815_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_896_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_896_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_896_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_896_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
uint8_t v_ring_832_; 
v_ring_832_ = lean_ctor_get_uint8(v_a_828_, sizeof(void*)*14 + 21);
lean_dec(v_a_828_);
if (v_ring_832_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_box(v_ring_832_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_876_);
v___x_878_ = v___x_830_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
if (lean_obj_tag(v_f_814_) == 4)
{
lean_object* v_declName_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
lean_del_object(v___x_830_);
v_declName_880_ = lean_ctor_get(v_f_814_, 0);
v___x_881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__2));
v___x_882_ = lean_name_eq(v_declName_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__5));
v___x_884_ = lean_name_eq(v_declName_880_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__8));
v___x_886_ = lean_name_eq(v_declName_880_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__11));
v___x_888_ = lean_name_eq(v_declName_880_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___closed__14));
v___x_890_ = lean_name_eq(v_declName_880_, v___x_889_);
if (v___x_890_ == 0)
{
goto v___jp_823_;
}
else
{
goto v___jp_833_;
}
}
else
{
goto v___jp_833_;
}
}
else
{
goto v___jp_833_;
}
}
else
{
goto v___jp_833_;
}
}
else
{
goto v___jp_833_;
}
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = 0;
v___x_892_ = lean_box(v___x_891_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_892_);
v___x_894_ = v___x_830_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_834_ = l_Lean_Expr_getAppNumArgs(v_op_813_);
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_dec_eq(v___x_834_, v___x_835_);
lean_dec(v___x_834_);
if (v___x_836_ == 0)
{
goto v___jp_823_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_837_ = l_Lean_Expr_appFn_x21(v_op_813_);
v___x_838_ = l_Lean_Expr_appFn_x21(v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_Expr_appArg_x21(v___x_838_);
lean_dec_ref(v___x_838_);
lean_inc_ref(v___x_839_);
v___x_840_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v___x_839_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_867_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
if (lean_obj_tag(v_a_841_) == 0)
{
lean_object* v___x_845_; 
lean_del_object(v___x_843_);
v___x_845_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v___x_839_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
if (lean_obj_tag(v_a_846_) == 0)
{
lean_del_object(v___x_848_);
goto v___jp_823_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_852_; 
lean_dec_ref_known(v_a_846_, 1);
v___x_850_ = lean_box(v_ring_832_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_845_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_dec_ref_known(v_a_841_, 1);
lean_dec_ref(v___x_839_);
v___x_863_ = lean_box(v_ring_832_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_863_);
v___x_865_ = v___x_843_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v___x_839_);
v_a_868_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_840_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_840_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_827_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_827_);
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
v___jp_823_:
{
uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = 0;
v___x_825_ = lean_box(v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_813_ = stack[0].m_obj;
lean_object* v_f_814_ = stack[1].m_obj;
lean_object* v_a_815_ = stack[2].m_obj;
lean_object* v_a_816_ = stack[3].m_obj;
lean_object* v_a_817_ = stack[4].m_obj;
lean_object* v_a_818_ = stack[5].m_obj;
lean_object* v_a_819_ = stack[6].m_obj;
lean_object* v_a_820_ = stack[7].m_obj;
lean_object* v_a_821_ = stack[8].m_obj;
lean_object* v_res_905_;
v_res_905_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_813_, v_f_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
stack->m_obj
 = v_res_905_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg___boxed(lean_object* v_op_906_, lean_object* v_f_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_906_, v_f_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_f_907_);
lean_dec_ref(v_op_906_);
return v_res_916_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* v_op_917_, lean_object* v_f_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_917_, v_f_918_, v_a_921_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_930_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_917_ = stack[0].m_obj;
lean_object* v_f_918_ = stack[1].m_obj;
lean_object* v_a_919_ = stack[2].m_obj;
lean_object* v_a_920_ = stack[3].m_obj;
lean_object* v_a_921_ = stack[4].m_obj;
lean_object* v_a_922_ = stack[5].m_obj;
lean_object* v_a_923_ = stack[6].m_obj;
lean_object* v_a_924_ = stack[7].m_obj;
lean_object* v_a_925_ = stack[8].m_obj;
lean_object* v_a_926_ = stack[9].m_obj;
lean_object* v_a_927_ = stack[10].m_obj;
lean_object* v_a_928_ = stack[11].m_obj;
lean_object* v_res_931_;
v_res_931_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_917_, v_f_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* v_op_932_, lean_object* v_f_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_932_, v_f_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_f_933_);
lean_dec_ref(v_op_932_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_i_948_, lean_object* v_k_949_){
_start:
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_array_get_size(v_keys_946_);
v___x_951_ = lean_nat_dec_lt(v_i_948_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_i_948_);
v___x_952_ = lean_box(0);
return v___x_952_;
}
else
{
lean_object* v_k_x27_953_; size_t v___x_954_; size_t v___x_955_; uint8_t v___x_956_; 
v_k_x27_953_ = lean_array_fget_borrowed(v_keys_946_, v_i_948_);
v___x_954_ = lean_ptr_addr(v_k_949_);
v___x_955_ = lean_ptr_addr(v_k_x27_953_);
v___x_956_ = lean_usize_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_add(v_i_948_, v___x_957_);
lean_dec(v_i_948_);
v_i_948_ = v___x_958_;
goto _start;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_array_fget_borrowed(v_vals_947_, v_i_948_);
lean_dec(v_i_948_);
lean_inc(v___x_960_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_i_964_, lean_object* v_k_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_962_, v_vals_963_, v_i_964_, v_k_965_);
lean_dec_ref(v_k_965_);
lean_dec_ref(v_vals_963_);
lean_dec_ref(v_keys_962_);
return v_res_966_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* v_x_967_, size_t v_x_968_, lean_object* v_x_969_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
lean_object* v_es_970_; lean_object* v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v_j_974_; lean_object* v___x_975_; 
v_es_970_ = lean_ctor_get(v_x_967_, 0);
v___x_971_ = lean_box(2);
v___x_972_ = ((size_t)31ULL);
v___x_973_ = lean_usize_land(v_x_968_, v___x_972_);
v_j_974_ = lean_usize_to_nat(v___x_973_);
v___x_975_ = lean_array_get_borrowed(v___x_971_, v_es_970_, v_j_974_);
lean_dec(v_j_974_);
switch(lean_obj_tag(v___x_975_))
{
case 0:
{
lean_object* v_key_976_; lean_object* v_val_977_; size_t v___x_978_; size_t v___x_979_; uint8_t v___x_980_; 
v_key_976_ = lean_ctor_get(v___x_975_, 0);
v_val_977_ = lean_ctor_get(v___x_975_, 1);
v___x_978_ = lean_ptr_addr(v_x_969_);
v___x_979_ = lean_ptr_addr(v_key_976_);
v___x_980_ = lean_usize_dec_eq(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_box(0);
return v___x_981_;
}
else
{
lean_object* v___x_982_; 
lean_inc(v_val_977_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_val_977_);
return v___x_982_;
}
}
case 1:
{
lean_object* v_node_983_; size_t v___x_984_; size_t v___x_985_; 
v_node_983_ = lean_ctor_get(v___x_975_, 0);
v___x_984_ = ((size_t)5ULL);
v___x_985_ = lean_usize_shift_right(v_x_968_, v___x_984_);
v_x_967_ = v_node_983_;
v_x_968_ = v___x_985_;
goto _start;
}
default: 
{
lean_object* v___x_987_; 
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
else
{
lean_object* v_ks_988_; lean_object* v_vs_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_ks_988_ = lean_ctor_get(v_x_967_, 0);
v_vs_989_ = lean_ctor_get(v_x_967_, 1);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_988_, v_vs_989_, v___x_990_, v_x_969_);
return v___x_991_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_967_ = stack[0].m_obj;
size_t v_x_968_ = stack[1].m_num;
lean_object* v_x_969_ = stack[2].m_obj;
lean_object* v_res_992_;
v_res_992_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_967_, v_x_968_, v_x_969_);
stack->m_obj
 = v_res_992_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_998__boxed_996_; lean_object* v_res_997_; 
v_x_998__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_993_, v_x_998__boxed_996_, v_x_995_);
lean_dec_ref(v_x_995_);
lean_dec_ref(v_x_993_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; uint64_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1000_ = lean_ptr_addr(v_x_999_);
v___x_1001_ = ((size_t)3ULL);
v___x_1002_ = lean_usize_shift_right(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_usize_to_uint64(v___x_1002_);
v___x_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_998_, v___x_1004_, v_x_999_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1006_, v_x_1007_);
lean_dec_ref(v_x_1007_);
lean_dec_ref(v_x_1006_);
return v_res_1008_;
}
}
lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* v_e_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1028_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1028_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_exprToOpIds_1018_; lean_object* v___x_1019_; 
v_exprToOpIds_1018_ = lean_ctor_get(v_a_1014_, 2);
lean_inc_ref(v_exprToOpIds_1018_);
lean_dec(v_a_1014_);
v___x_1019_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_1018_, v_e_1009_);
lean_dec_ref(v_exprToOpIds_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1020_);
v___x_1022_ = v___x_1016_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1026_; 
v_val_1024_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v___x_1019_, 1);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v_val_1024_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_val_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1013_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1013_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getTermOpIds___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1009_ = stack[0].m_obj;
lean_object* v_a_1010_ = stack[1].m_obj;
lean_object* v_a_1011_ = stack[2].m_obj;
lean_object* v_res_1037_;
v_res_1037_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1009_, v_a_1010_, v_a_1011_);
stack->m_obj
 = v_res_1037_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1038_, v_a_1039_, v_a_1040_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_e_1038_);
return v_res_1042_;
}
}
lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* v_e_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_1043_, v_a_1044_, v_a_1052_);
return v___x_1055_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getTermOpIds_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1043_ = stack[0].m_obj;
lean_object* v_a_1044_ = stack[1].m_obj;
lean_object* v_a_1045_ = stack[2].m_obj;
lean_object* v_a_1046_ = stack[3].m_obj;
lean_object* v_a_1047_ = stack[4].m_obj;
lean_object* v_a_1048_ = stack[5].m_obj;
lean_object* v_a_1049_ = stack[6].m_obj;
lean_object* v_a_1050_ = stack[7].m_obj;
lean_object* v_a_1051_ = stack[8].m_obj;
lean_object* v_a_1052_ = stack[9].m_obj;
lean_object* v_a_1053_ = stack[10].m_obj;
lean_object* v_res_1056_;
v_res_1056_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
stack->m_obj
 = v_res_1056_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* v_e_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_e_1057_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(v_00_u03b2_1074_, v_x_1075_, v_x_1076_);
lean_dec_ref(v_x_1076_);
lean_dec_ref(v_x_1075_);
return v_res_1077_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1079_ = stack[1].m_obj;
size_t v_x_1080_ = stack[2].m_num;
lean_object* v_x_1081_ = stack[3].m_obj;
lean_object* v_res_1083_;
v_res_1083_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_box(0), v_x_1079_, v_x_1080_, v_x_1081_);
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
size_t v_x_1199__boxed_1088_; lean_object* v_res_1089_; 
v_x_1199__boxed_1088_ = lean_unbox_usize(v_x_1086_);
lean_dec(v_x_1086_);
v_res_1089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_1084_, v_x_1085_, v_x_1199__boxed_1088_, v_x_1087_);
lean_dec_ref(v_x_1087_);
lean_dec_ref(v_x_1085_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1091_, v_vals_1092_, v_i_1094_, v_k_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_keys_1098_, lean_object* v_vals_1099_, lean_object* v_heq_1100_, lean_object* v_i_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_1097_, v_keys_1098_, v_vals_1099_, v_heq_1100_, v_i_1101_, v_k_1102_);
lean_dec_ref(v_k_1102_);
lean_dec_ref(v_vals_1099_);
lean_dec_ref(v_keys_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* v_opId_1104_, lean_object* v_a_1105_){
_start:
{
if (lean_obj_tag(v_a_1105_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_opId_1104_);
lean_ctor_set(v___x_1106_, 1, v_a_1105_);
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; uint8_t v___x_1109_; 
v_head_1107_ = lean_ctor_get(v_a_1105_, 0);
v_tail_1108_ = lean_ctor_get(v_a_1105_, 1);
v___x_1109_ = lean_nat_dec_lt(v_opId_1104_, v_head_1107_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1121_; 
lean_inc(v_tail_1108_);
lean_inc(v_head_1107_);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1122_ = lean_ctor_get(v_a_1105_, 1);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_a_1105_, 0);
lean_dec(v_unused_1123_);
v___x_1111_ = v_a_1105_;
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v_a_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_nat_dec_eq(v_opId_1104_, v_head_1107_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1104_, v_tail_1108_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_head_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_head_1107_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v_opId_1104_);
v___x_1119_ = v___x_1111_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_opId_1104_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_tail_1108_);
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
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_opId_1104_);
lean_ctor_set(v___x_1124_, 1, v_a_1105_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_ks_1129_; lean_object* v_vs_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1156_; 
v_ks_1129_ = lean_ctor_get(v_x_1125_, 0);
v_vs_1130_ = lean_ctor_get(v_x_1125_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1132_ = v_x_1125_;
v_isShared_1133_ = v_isSharedCheck_1156_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_vs_1130_);
lean_inc(v_ks_1129_);
lean_dec(v_x_1125_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1156_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_array_get_size(v_ks_1129_);
v___x_1135_ = lean_nat_dec_lt(v_x_1126_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec(v_x_1126_);
v___x_1136_ = lean_array_push(v_ks_1129_, v_x_1127_);
v___x_1137_ = lean_array_push(v_vs_1130_, v_x_1128_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1137_);
lean_ctor_set(v___x_1132_, 0, v___x_1136_);
v___x_1139_ = v___x_1132_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
lean_object* v_k_x27_1141_; size_t v___x_1142_; size_t v___x_1143_; uint8_t v___x_1144_; 
v_k_x27_1141_ = lean_array_fget_borrowed(v_ks_1129_, v_x_1126_);
v___x_1142_ = lean_ptr_addr(v_x_1127_);
v___x_1143_ = lean_ptr_addr(v_k_x27_1141_);
v___x_1144_ = lean_usize_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1146_; 
if (v_isShared_1133_ == 0)
{
v___x_1146_ = v___x_1132_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_ks_1129_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_vs_1130_);
v___x_1146_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_add(v_x_1126_, v___x_1147_);
lean_dec(v_x_1126_);
v_x_1125_ = v___x_1146_;
v_x_1126_ = v___x_1148_;
goto _start;
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = lean_array_fset(v_ks_1129_, v_x_1126_, v_x_1127_);
v___x_1152_ = lean_array_fset(v_vs_1130_, v_x_1126_, v_x_1128_);
lean_dec(v_x_1126_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1152_);
lean_ctor_set(v___x_1132_, 0, v___x_1151_);
v___x_1154_ = v___x_1132_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1157_, lean_object* v_k_1158_, lean_object* v_v_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1157_, v___x_1160_, v_k_1158_, v_v_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1162_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* v_x_1163_, size_t v_x_1164_, size_t v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v_es_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v_j_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_es_1168_ = lean_ctor_get(v_x_1163_, 0);
v___x_1169_ = ((size_t)31ULL);
v___x_1170_ = lean_usize_land(v_x_1164_, v___x_1169_);
v_j_1171_ = lean_usize_to_nat(v___x_1170_);
v___x_1172_ = lean_array_get_size(v_es_1168_);
v___x_1173_ = lean_nat_dec_lt(v_j_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_j_1171_);
lean_dec(v_x_1167_);
lean_dec_ref(v_x_1166_);
return v_x_1163_;
}
else
{
lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1214_; 
lean_inc_ref(v_es_1168_);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1163_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_x_1163_, 0);
lean_dec(v_unused_1215_);
v___x_1175_ = v_x_1163_;
v_isShared_1176_ = v_isSharedCheck_1214_;
goto v_resetjp_1174_;
}
else
{
lean_dec(v_x_1163_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1214_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_v_1177_; lean_object* v___x_1178_; lean_object* v_xs_x27_1179_; lean_object* v___y_1181_; 
v_v_1177_ = lean_array_fget(v_es_1168_, v_j_1171_);
v___x_1178_ = lean_box(0);
v_xs_x27_1179_ = lean_array_fset(v_es_1168_, v_j_1171_, v___x_1178_);
switch(lean_obj_tag(v_v_1177_))
{
case 0:
{
lean_object* v_key_1186_; lean_object* v_val_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1199_; 
v_key_1186_ = lean_ctor_get(v_v_1177_, 0);
v_val_1187_ = lean_ctor_get(v_v_1177_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_v_1177_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1189_ = v_v_1177_;
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_val_1187_);
lean_inc(v_key_1186_);
lean_dec(v_v_1177_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
size_t v___x_1191_; size_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_ptr_addr(v_x_1166_);
v___x_1192_ = lean_ptr_addr(v_key_1186_);
v___x_1193_ = lean_usize_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_del_object(v___x_1189_);
v___x_1194_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1186_, v_val_1187_, v_x_1166_, v_x_1167_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
v___y_1181_ = v___x_1195_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1197_; 
lean_dec(v_val_1187_);
lean_dec(v_key_1186_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v_x_1167_);
lean_ctor_set(v___x_1189_, 0, v_x_1166_);
v___x_1197_ = v___x_1189_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_x_1166_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_x_1167_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v___y_1181_ = v___x_1197_;
goto v___jp_1180_;
}
}
}
}
case 1:
{
lean_object* v_node_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1212_; 
v_node_1200_ = lean_ctor_get(v_v_1177_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_v_1177_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1202_ = v_v_1177_;
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_node_1200_);
lean_dec(v_v_1177_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1204_ = ((size_t)5ULL);
v___x_1205_ = lean_usize_shift_right(v_x_1164_, v___x_1204_);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_x_1165_, v___x_1206_);
v___x_1208_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_1200_, v___x_1205_, v___x_1207_, v_x_1166_, v_x_1167_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1210_ = v___x_1202_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
v___y_1181_ = v___x_1210_;
goto v___jp_1180_;
}
}
}
default: 
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_x_1166_);
lean_ctor_set(v___x_1213_, 1, v_x_1167_);
v___y_1181_ = v___x_1213_;
goto v___jp_1180_;
}
}
v___jp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_array_fset(v_xs_x27_1179_, v_j_1171_, v___y_1181_);
lean_dec(v_j_1171_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1182_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v_ks_1216_; lean_object* v_vs_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1235_; 
v_ks_1216_ = lean_ctor_get(v_x_1163_, 0);
v_vs_1217_ = lean_ctor_get(v_x_1163_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_x_1163_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1219_ = v_x_1163_;
v_isShared_1220_ = v_isSharedCheck_1235_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_vs_1217_);
lean_inc(v_ks_1216_);
lean_dec(v_x_1163_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1235_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_ks_1216_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_vs_1217_);
v___x_1222_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v_newNode_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v_newNode_1223_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_1222_, v_x_1166_, v_x_1167_);
v___x_1224_ = ((size_t)7ULL);
v___x_1225_ = lean_usize_dec_le(v___x_1224_, v_x_1165_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1226_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1223_);
v___x_1227_ = lean_unsigned_to_nat(4u);
v___x_1228_ = lean_nat_dec_lt(v___x_1226_, v___x_1227_);
lean_dec(v___x_1226_);
if (v___x_1228_ == 0)
{
lean_object* v_ks_1229_; lean_object* v_vs_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_ks_1229_ = lean_ctor_get(v_newNode_1223_, 0);
lean_inc_ref(v_ks_1229_);
v_vs_1230_ = lean_ctor_get(v_newNode_1223_, 1);
lean_inc_ref(v_vs_1230_);
lean_dec_ref(v_newNode_1223_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
v___x_1233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_1165_, v_ks_1229_, v_vs_1230_, v___x_1231_, v___x_1232_);
lean_dec_ref(v_vs_1230_);
lean_dec_ref(v_ks_1229_);
return v___x_1233_;
}
else
{
return v_newNode_1223_;
}
}
else
{
return v_newNode_1223_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1163_ = stack[0].m_obj;
size_t v_x_1164_ = stack[1].m_num;
size_t v_x_1165_ = stack[2].m_num;
lean_object* v_x_1166_ = stack[3].m_obj;
lean_object* v_x_1167_ = stack[4].m_obj;
lean_object* v_res_1236_;
v_res_1236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1163_, v_x_1164_, v_x_1165_, v_x_1166_, v_x_1167_);
stack->m_obj
 = v_res_1236_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1237_, lean_object* v_keys_1238_, lean_object* v_vals_1239_, lean_object* v_i_1240_, lean_object* v_entries_1241_){
_start:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_array_get_size(v_keys_1238_);
v___x_1243_ = lean_nat_dec_lt(v_i_1240_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v_i_1240_);
return v_entries_1241_;
}
else
{
lean_object* v_k_1244_; lean_object* v_v_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; uint64_t v___x_1249_; size_t v_h_1250_; size_t v___x_1251_; lean_object* v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; size_t v_h_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_k_1244_ = lean_array_fget_borrowed(v_keys_1238_, v_i_1240_);
v_v_1245_ = lean_array_fget_borrowed(v_vals_1239_, v_i_1240_);
v___x_1246_ = lean_ptr_addr(v_k_1244_);
v___x_1247_ = ((size_t)3ULL);
v___x_1248_ = lean_usize_shift_right(v___x_1246_, v___x_1247_);
v___x_1249_ = lean_usize_to_uint64(v___x_1248_);
v_h_1250_ = lean_uint64_to_usize(v___x_1249_);
v___x_1251_ = ((size_t)5ULL);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = lean_usize_sub(v_depth_1237_, v___x_1253_);
v___x_1255_ = lean_usize_mul(v___x_1251_, v___x_1254_);
v_h_1256_ = lean_usize_shift_right(v_h_1250_, v___x_1255_);
v___x_1257_ = lean_nat_add(v_i_1240_, v___x_1252_);
lean_dec(v_i_1240_);
lean_inc(v_v_1245_);
lean_inc(v_k_1244_);
v___x_1258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_1241_, v_h_1256_, v_depth_1237_, v_k_1244_, v_v_1245_);
v_i_1240_ = v___x_1257_;
v_entries_1241_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1237_ = stack[0].m_num;
lean_object* v_keys_1238_ = stack[1].m_obj;
lean_object* v_vals_1239_ = stack[2].m_obj;
lean_object* v_i_1240_ = stack[3].m_obj;
lean_object* v_entries_1241_ = stack[4].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1237_, v_keys_1238_, v_vals_1239_, v_i_1240_, v_entries_1241_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1261_, lean_object* v_keys_1262_, lean_object* v_vals_1263_, lean_object* v_i_1264_, lean_object* v_entries_1265_){
_start:
{
size_t v_depth_boxed_1266_; lean_object* v_res_1267_; 
v_depth_boxed_1266_ = lean_unbox_usize(v_depth_1261_);
lean_dec(v_depth_1261_);
v_res_1267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1266_, v_keys_1262_, v_vals_1263_, v_i_1264_, v_entries_1265_);
lean_dec_ref(v_vals_1263_);
lean_dec_ref(v_keys_1262_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
size_t v_x_476__boxed_1273_; size_t v_x_477__boxed_1274_; lean_object* v_res_1275_; 
v_x_476__boxed_1273_ = lean_unbox_usize(v_x_1269_);
lean_dec(v_x_1269_);
v_x_477__boxed_1274_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_res_1275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1268_, v_x_476__boxed_1273_, v_x_477__boxed_1274_, v_x_1271_, v_x_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; uint64_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1279_ = lean_ptr_addr(v_x_1277_);
v___x_1280_ = ((size_t)3ULL);
v___x_1281_ = lean_usize_shift_right(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_usize_to_uint64(v___x_1281_);
v___x_1283_ = lean_uint64_to_usize(v___x_1282_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1276_, v___x_1283_, v___x_1284_, v_x_1277_, v_x_1278_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* v_m_1286_, lean_object* v_e_1287_, lean_object* v_opId_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_m_1286_, v_e_1287_);
if (lean_obj_tag(v___x_1289_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1291_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1288_, v_val_1290_);
v___x_1292_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1286_, v_e_1287_, v___x_1291_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec(v___x_1289_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_opId_1288_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1286_, v_e_1287_, v___x_1294_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_1297_, v_x_1298_, v_x_1299_);
return v___x_1300_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* v_00_u03b2_1301_, lean_object* v_x_1302_, size_t v_x_1303_, size_t v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1302_, v_x_1303_, v_x_1304_, v_x_1305_, v_x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1302_ = stack[1].m_obj;
size_t v_x_1303_ = stack[2].m_num;
size_t v_x_1304_ = stack[3].m_num;
lean_object* v_x_1305_ = stack[4].m_obj;
lean_object* v_x_1306_ = stack[5].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_box(0), v_x_1302_, v_x_1303_, v_x_1304_, v_x_1305_, v_x_1306_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_){
_start:
{
size_t v_x_787__boxed_1315_; size_t v_x_788__boxed_1316_; lean_object* v_res_1317_; 
v_x_787__boxed_1315_ = lean_unbox_usize(v_x_1311_);
lean_dec(v_x_1311_);
v_x_788__boxed_1316_ = lean_unbox_usize(v_x_1312_);
lean_dec(v_x_1312_);
v_res_1317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_1309_, v_x_1310_, v_x_787__boxed_1315_, v_x_788__boxed_1316_, v_x_1313_, v_x_1314_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1318_, lean_object* v_n_1319_, lean_object* v_k_1320_, lean_object* v_v_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_1319_, v_k_1320_, v_v_1321_);
return v___x_1322_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1323_, size_t v_depth_1324_, lean_object* v_keys_1325_, lean_object* v_vals_1326_, lean_object* v_heq_1327_, lean_object* v_i_1328_, lean_object* v_entries_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1324_, v_keys_1325_, v_vals_1326_, v_i_1328_, v_entries_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1324_ = stack[1].m_num;
lean_object* v_keys_1325_ = stack[2].m_obj;
lean_object* v_vals_1326_ = stack[3].m_obj;
lean_object* v_i_1328_ = stack[5].m_obj;
lean_object* v_entries_1329_ = stack[6].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_box(0), v_depth_1324_, v_keys_1325_, v_vals_1326_, lean_box(0), v_i_1328_, v_entries_1329_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1332_, lean_object* v_depth_1333_, lean_object* v_keys_1334_, lean_object* v_vals_1335_, lean_object* v_heq_1336_, lean_object* v_i_1337_, lean_object* v_entries_1338_){
_start:
{
size_t v_depth_boxed_1339_; lean_object* v_res_1340_; 
v_depth_boxed_1339_ = lean_unbox_usize(v_depth_1333_);
lean_dec(v_depth_1333_);
v_res_1340_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_1332_, v_depth_boxed_1339_, v_keys_1334_, v_vals_1335_, v_heq_1336_, v_i_1337_, v_entries_1338_);
lean_dec_ref(v_vals_1335_);
lean_dec_ref(v_keys_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1342_, v_x_1343_, v_x_1344_, v_x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v_s_1349_){
_start:
{
lean_object* v_structs_1350_; lean_object* v_opIdOf_1351_; lean_object* v_exprToOpIds_1352_; lean_object* v_steps_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_structs_1350_ = lean_ctor_get(v_s_1349_, 0);
v_opIdOf_1351_ = lean_ctor_get(v_s_1349_, 1);
v_exprToOpIds_1352_ = lean_ctor_get(v_s_1349_, 2);
v_steps_1353_ = lean_ctor_get(v_s_1349_, 3);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_s_1349_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_s_1349_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_steps_1353_);
lean_inc(v_exprToOpIds_1352_);
lean_inc(v_opIdOf_1351_);
lean_inc(v_structs_1350_);
lean_dec(v_s_1349_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_inc(v_a_1348_);
v___x_1357_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(v_exprToOpIds_1352_, v_e_1347_, v_a_1348_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 2, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_structs_1350_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_opIdOf_1351_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_steps_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object* v_e_1362_, lean_object* v_a_1363_, lean_object* v_s_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_1362_, v_a_1363_, v_s_1364_);
lean_dec(v_a_1363_);
return v_res_1365_;
}
}
lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* v_e_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___f_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_inc(v_a_1367_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1370_, 0, v_e_1366_);
lean_closure_set(v___f_1370_, 1, v_a_1367_);
v___x_1371_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1372_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1371_, v___f_1370_, v_a_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_addTermOpId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1366_ = stack[0].m_obj;
lean_object* v_a_1367_ = stack[1].m_obj;
lean_object* v_a_1368_ = stack[2].m_obj;
lean_object* v_res_1373_;
v_res_1373_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1366_, v_a_1367_, v_a_1368_);
stack->m_obj
 = v_res_1373_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* v_e_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
return v_res_1378_;
}
}
lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* v_e_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1379_, v_a_1380_, v_a_1381_);
return v___x_1392_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_addTermOpId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1379_ = stack[0].m_obj;
lean_object* v_a_1380_ = stack[1].m_obj;
lean_object* v_a_1381_ = stack[2].m_obj;
lean_object* v_a_1382_ = stack[3].m_obj;
lean_object* v_a_1383_ = stack[4].m_obj;
lean_object* v_a_1384_ = stack[5].m_obj;
lean_object* v_a_1385_ = stack[6].m_obj;
lean_object* v_a_1386_ = stack[7].m_obj;
lean_object* v_a_1387_ = stack[8].m_obj;
lean_object* v_a_1388_ = stack[9].m_obj;
lean_object* v_a_1389_ = stack[10].m_obj;
lean_object* v_a_1390_ = stack[11].m_obj;
lean_object* v_res_1393_;
v_res_1393_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
stack->m_obj
 = v_res_1393_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec(v_a_1395_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* v_e_1408_, lean_object* v_size_1409_, lean_object* v_s_1410_){
_start:
{
lean_object* v_id_1411_; lean_object* v_type_1412_; lean_object* v_u_1413_; lean_object* v_op_1414_; lean_object* v_neutral_x3f_1415_; lean_object* v_assocInst_1416_; lean_object* v_idempotentInst_x3f_1417_; lean_object* v_commInst_x3f_1418_; lean_object* v_neutralInst_x3f_1419_; lean_object* v_nextId_1420_; lean_object* v_vars_1421_; lean_object* v_varMap_1422_; lean_object* v_denote_1423_; lean_object* v_denoteEntries_1424_; lean_object* v_queue_1425_; lean_object* v_basis_1426_; lean_object* v_diseqs_1427_; uint8_t v_recheck_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v_id_1411_ = lean_ctor_get(v_s_1410_, 0);
v_type_1412_ = lean_ctor_get(v_s_1410_, 1);
v_u_1413_ = lean_ctor_get(v_s_1410_, 2);
v_op_1414_ = lean_ctor_get(v_s_1410_, 3);
v_neutral_x3f_1415_ = lean_ctor_get(v_s_1410_, 4);
v_assocInst_1416_ = lean_ctor_get(v_s_1410_, 5);
v_idempotentInst_x3f_1417_ = lean_ctor_get(v_s_1410_, 6);
v_commInst_x3f_1418_ = lean_ctor_get(v_s_1410_, 7);
v_neutralInst_x3f_1419_ = lean_ctor_get(v_s_1410_, 8);
v_nextId_1420_ = lean_ctor_get(v_s_1410_, 9);
v_vars_1421_ = lean_ctor_get(v_s_1410_, 10);
v_varMap_1422_ = lean_ctor_get(v_s_1410_, 11);
v_denote_1423_ = lean_ctor_get(v_s_1410_, 12);
v_denoteEntries_1424_ = lean_ctor_get(v_s_1410_, 13);
v_queue_1425_ = lean_ctor_get(v_s_1410_, 14);
v_basis_1426_ = lean_ctor_get(v_s_1410_, 15);
v_diseqs_1427_ = lean_ctor_get(v_s_1410_, 16);
v_recheck_1428_ = lean_ctor_get_uint8(v_s_1410_, sizeof(void*)*17);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_s_1410_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v_s_1410_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_diseqs_1427_);
lean_inc(v_basis_1426_);
lean_inc(v_queue_1425_);
lean_inc(v_denoteEntries_1424_);
lean_inc(v_denote_1423_);
lean_inc(v_varMap_1422_);
lean_inc(v_vars_1421_);
lean_inc(v_nextId_1420_);
lean_inc(v_neutralInst_x3f_1419_);
lean_inc(v_commInst_x3f_1418_);
lean_inc(v_idempotentInst_x3f_1417_);
lean_inc(v_assocInst_1416_);
lean_inc(v_neutral_x3f_1415_);
lean_inc(v_op_1414_);
lean_inc(v_u_1413_);
lean_inc(v_type_1412_);
lean_inc(v_id_1411_);
lean_dec(v_s_1410_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc_ref(v_e_1408_);
v___x_1432_ = l_Lean_PersistentArray_push___redArg(v_vars_1421_, v_e_1408_);
v___x_1433_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_1422_, v_e_1408_, v_size_1409_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 11, v___x_1433_);
lean_ctor_set(v___x_1430_, 10, v___x_1432_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_id_1411_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_type_1412_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_u_1413_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_op_1414_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v_neutral_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1436_, 5, v_assocInst_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 6, v_idempotentInst_x3f_1417_);
lean_ctor_set(v_reuseFailAlloc_1436_, 7, v_commInst_x3f_1418_);
lean_ctor_set(v_reuseFailAlloc_1436_, 8, v_neutralInst_x3f_1419_);
lean_ctor_set(v_reuseFailAlloc_1436_, 9, v_nextId_1420_);
lean_ctor_set(v_reuseFailAlloc_1436_, 10, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1436_, 11, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 12, v_denote_1423_);
lean_ctor_set(v_reuseFailAlloc_1436_, 13, v_denoteEntries_1424_);
lean_ctor_set(v_reuseFailAlloc_1436_, 14, v_queue_1425_);
lean_ctor_set(v_reuseFailAlloc_1436_, 15, v_basis_1426_);
lean_ctor_set(v_reuseFailAlloc_1436_, 16, v_diseqs_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, sizeof(void*)*17, v_recheck_1428_);
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
lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* v_e_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1501_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1501_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1501_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_vars_1456_; lean_object* v_varMap_1457_; lean_object* v___x_1458_; 
v_vars_1456_ = lean_ctor_get(v_a_1452_, 10);
lean_inc_ref(v_vars_1456_);
v_varMap_1457_ = lean_ctor_get(v_a_1452_, 11);
lean_inc_ref(v_varMap_1457_);
lean_dec(v_a_1452_);
v___x_1458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_1457_, v_e_1438_);
lean_dec_ref(v_varMap_1457_);
if (lean_obj_tag(v___x_1458_) == 1)
{
lean_object* v_val_1459_; lean_object* v___x_1461_; 
lean_dec_ref(v_vars_1456_);
lean_dec_ref(v_e_1438_);
v_val_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v___x_1458_, 1);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v_val_1459_);
v___x_1461_ = v___x_1454_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_val_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
else
{
lean_object* v_size_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; 
lean_dec(v___x_1458_);
lean_del_object(v___x_1454_);
v_size_1463_ = lean_ctor_get(v_vars_1456_, 2);
lean_inc_n(v_size_1463_, 2);
lean_dec_ref(v_vars_1456_);
lean_inc_ref(v_e_1438_);
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(v___f_1464_, 0, v_e_1438_);
lean_closure_set(v___f_1464_, 1, v_size_1463_);
v___x_1465_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_1464_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref_known(v___x_1465_, 1);
lean_inc_ref(v_e_1438_);
v___x_1466_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref_known(v___x_1466_, 1);
v___x_1467_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1468_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1467_, v_e_1438_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1476_);
v___x_1470_ = v___x_1468_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v___x_1468_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_size_1463_);
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_size_1463_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_size_1463_);
v_a_1477_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1468_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1468_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_size_1463_);
lean_dec_ref(v_e_1438_);
v_a_1485_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1466_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1466_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_size_1463_);
lean_dec_ref(v_e_1438_);
v_a_1493_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1465_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1465_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec_ref(v_e_1438_);
v_a_1502_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1451_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1451_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_mkVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1438_ = stack[0].m_obj;
lean_object* v_a_1439_ = stack[1].m_obj;
lean_object* v_a_1440_ = stack[2].m_obj;
lean_object* v_a_1441_ = stack[3].m_obj;
lean_object* v_a_1442_ = stack[4].m_obj;
lean_object* v_a_1443_ = stack[5].m_obj;
lean_object* v_a_1444_ = stack[6].m_obj;
lean_object* v_a_1445_ = stack[7].m_obj;
lean_object* v_a_1446_ = stack[8].m_obj;
lean_object* v_a_1447_ = stack[9].m_obj;
lean_object* v_a_1448_ = stack[10].m_obj;
lean_object* v_a_1449_ = stack[11].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec(v_a_1512_);
return v_res_1524_;
}
}
lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* v_e_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v_mctx_1529_; lean_object* v___x_1530_; lean_object* v_fst_1531_; lean_object* v_snd_1532_; lean_object* v___x_1533_; lean_object* v_cache_1534_; lean_object* v_zetaDeltaFVarIds_1535_; lean_object* v_postponed_1536_; lean_object* v_diag_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
v___x_1528_ = lean_st_ref_get(v___y_1526_);
v_mctx_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc_ref(v_mctx_1529_);
lean_dec(v___x_1528_);
v___x_1530_ = lean_instantiate_expr_mvars(v_mctx_1529_, v_e_1525_);
v_fst_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_fst_1531_);
v_snd_1532_ = lean_ctor_get(v___x_1530_, 1);
lean_inc(v_snd_1532_);
lean_dec_ref(v___x_1530_);
v___x_1533_ = lean_st_ref_take(v___y_1526_);
v_cache_1534_ = lean_ctor_get(v___x_1533_, 1);
v_zetaDeltaFVarIds_1535_ = lean_ctor_get(v___x_1533_, 2);
v_postponed_1536_ = lean_ctor_get(v___x_1533_, 3);
v_diag_1537_ = lean_ctor_get(v___x_1533_, 4);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1533_, 0);
lean_dec(v_unused_1547_);
v___x_1539_ = v___x_1533_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_diag_1537_);
lean_inc(v_postponed_1536_);
lean_inc(v_zetaDeltaFVarIds_1535_);
lean_inc(v_cache_1534_);
lean_dec(v___x_1533_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_fst_1531_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_fst_1531_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_cache_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_zetaDeltaFVarIds_1535_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_postponed_1536_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_diag_1537_);
v___x_1542_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_st_ref_put(v___y_1526_, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_snd_1532_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1525_ = stack[0].m_obj;
lean_object* v___y_1526_ = stack[1].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1525_, v___y_1526_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* v_e_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1549_, v___y_1550_);
lean_dec(v___y_1550_);
return v_res_1552_;
}
}
lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* v_e_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1553_, v___y_1561_);
return v___x_1565_;
}
}
LEAN_EXPORT void l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1553_ = stack[0].m_obj;
lean_object* v___y_1554_ = stack[1].m_obj;
lean_object* v___y_1555_ = stack[2].m_obj;
lean_object* v___y_1556_ = stack[3].m_obj;
lean_object* v___y_1557_ = stack[4].m_obj;
lean_object* v___y_1558_ = stack[5].m_obj;
lean_object* v___y_1559_ = stack[6].m_obj;
lean_object* v___y_1560_ = stack[7].m_obj;
lean_object* v___y_1561_ = stack[8].m_obj;
lean_object* v___y_1562_ = stack[9].m_obj;
lean_object* v___y_1563_ = stack[10].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* v_e_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec(v___y_1568_);
return v_res_1579_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_unsigned_to_nat(32u);
v___x_1581_ = lean_mk_empty_array_with_capacity(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1(void){
_start:
{
size_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1583_ = ((size_t)5ULL);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_unsigned_to_nat(32u);
v___x_1586_ = lean_mk_empty_array_with_capacity(v___x_1585_);
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
v___x_1588_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1586_);
lean_ctor_set(v___x_1588_, 2, v___x_1584_);
lean_ctor_set(v___x_1588_, 3, v___x_1584_);
lean_ctor_set_usize(v___x_1588_, 4, v___x_1583_);
return v___x_1588_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1589_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* v___x_1592_, lean_object* v_binderType_1593_, lean_object* v_a_1594_, lean_object* v_op_1595_, lean_object* v_snd_1596_, lean_object* v_val_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_fst_1600_, uint8_t v_a_1601_, lean_object* v_s_1602_){
_start:
{
lean_object* v_structs_1603_; lean_object* v_opIdOf_1604_; lean_object* v_exprToOpIds_1605_; lean_object* v_steps_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1620_; 
v_structs_1603_ = lean_ctor_get(v_s_1602_, 0);
v_opIdOf_1604_ = lean_ctor_get(v_s_1602_, 1);
v_exprToOpIds_1605_ = lean_ctor_get(v_s_1602_, 2);
v_steps_1606_ = lean_ctor_get(v_s_1602_, 3);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_s_1602_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1608_ = v_s_1602_;
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_steps_1606_);
lean_inc(v_exprToOpIds_1605_);
lean_inc(v_opIdOf_1604_);
lean_inc(v_structs_1603_);
lean_dec(v_s_1602_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
v___x_1613_ = lean_box(1);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1592_);
lean_ctor_set(v___x_1615_, 1, v_binderType_1593_);
lean_ctor_set(v___x_1615_, 2, v_a_1594_);
lean_ctor_set(v___x_1615_, 3, v_op_1595_);
lean_ctor_set(v___x_1615_, 4, v_snd_1596_);
lean_ctor_set(v___x_1615_, 5, v_val_1597_);
lean_ctor_set(v___x_1615_, 6, v_a_1598_);
lean_ctor_set(v___x_1615_, 7, v_a_1599_);
lean_ctor_set(v___x_1615_, 8, v_fst_1600_);
lean_ctor_set(v___x_1615_, 9, v___x_1610_);
lean_ctor_set(v___x_1615_, 10, v___x_1611_);
lean_ctor_set(v___x_1615_, 11, v___x_1612_);
lean_ctor_set(v___x_1615_, 12, v___x_1612_);
lean_ctor_set(v___x_1615_, 13, v___x_1611_);
lean_ctor_set(v___x_1615_, 14, v___x_1613_);
lean_ctor_set(v___x_1615_, 15, v___x_1614_);
lean_ctor_set(v___x_1615_, 16, v___x_1611_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*17, v_a_1601_);
v___x_1616_ = lean_array_push(v_structs_1603_, v___x_1615_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1616_);
v___x_1618_ = v___x_1608_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_opIdOf_1604_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_exprToOpIds_1605_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_steps_1606_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1592_ = stack[0].m_obj;
lean_object* v_binderType_1593_ = stack[1].m_obj;
lean_object* v_a_1594_ = stack[2].m_obj;
lean_object* v_op_1595_ = stack[3].m_obj;
lean_object* v_snd_1596_ = stack[4].m_obj;
lean_object* v_val_1597_ = stack[5].m_obj;
lean_object* v_a_1598_ = stack[6].m_obj;
lean_object* v_a_1599_ = stack[7].m_obj;
lean_object* v_fst_1600_ = stack[8].m_obj;
uint8_t v_a_1601_ = stack[9].m_num;
lean_object* v_s_1602_ = stack[10].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1592_, v_binderType_1593_, v_a_1594_, v_op_1595_, v_snd_1596_, v_val_1597_, v_a_1598_, v_a_1599_, v_fst_1600_, v_a_1601_, v_s_1602_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* v___x_1622_, lean_object* v_binderType_1623_, lean_object* v_a_1624_, lean_object* v_op_1625_, lean_object* v_snd_1626_, lean_object* v_val_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_fst_1630_, lean_object* v_a_1631_, lean_object* v_s_1632_){
_start:
{
uint8_t v_a_121689__boxed_1633_; lean_object* v_res_1634_; 
v_a_121689__boxed_1633_ = lean_unbox(v_a_1631_);
v_res_1634_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1622_, v_binderType_1623_, v_a_1624_, v_op_1625_, v_snd_1626_, v_val_1627_, v_a_1628_, v_a_1629_, v_fst_1630_, v_a_121689__boxed_1633_, v_s_1632_);
return v_res_1634_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* v_m_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_buckets_1637_; lean_object* v___x_1638_; uint64_t v___y_1640_; 
v_buckets_1637_ = lean_ctor_get(v_m_1635_, 1);
v___x_1638_ = lean_array_get_size(v_buckets_1637_);
if (lean_obj_tag(v_a_1636_) == 0)
{
uint64_t v___x_1654_; 
v___x_1654_ = 1723ULL;
v___y_1640_ = v___x_1654_;
goto v___jp_1639_;
}
else
{
uint64_t v_hash_1655_; 
v_hash_1655_ = lean_ctor_get_uint64(v_a_1636_, sizeof(void*)*2);
v___y_1640_ = v_hash_1655_;
goto v___jp_1639_;
}
v___jp_1639_:
{
uint64_t v___x_1641_; uint64_t v___x_1642_; uint64_t v_fold_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; uint64_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1641_ = 32ULL;
v___x_1642_ = lean_uint64_shift_right(v___y_1640_, v___x_1641_);
v_fold_1643_ = lean_uint64_xor(v___y_1640_, v___x_1642_);
v___x_1644_ = 16ULL;
v___x_1645_ = lean_uint64_shift_right(v_fold_1643_, v___x_1644_);
v___x_1646_ = lean_uint64_xor(v_fold_1643_, v___x_1645_);
v___x_1647_ = lean_uint64_to_usize(v___x_1646_);
v___x_1648_ = lean_usize_of_nat(v___x_1638_);
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_sub(v___x_1648_, v___x_1649_);
v___x_1651_ = lean_usize_land(v___x_1647_, v___x_1650_);
v___x_1652_ = lean_array_uget_borrowed(v_buckets_1637_, v___x_1651_);
v___x_1653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_1636_, v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1635_ = stack[0].m_obj;
lean_object* v_a_1636_ = stack[1].m_obj;
uint8_t v_res_1656_;
v_res_1656_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1635_, v_a_1636_);
stack->m_num = v_res_1656_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* v_m_1657_, lean_object* v_a_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_m_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1661_; double v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_float_of_nat(v___x_1661_);
return v___x_1662_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* v_cls_1666_, lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_ref_1673_; lean_object* v___x_1674_; lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1720_; 
v_ref_1673_ = lean_ctor_get(v___y_1670_, 2);
v___x_1674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1720_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1720_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v_traceState_1680_; lean_object* v_env_1681_; lean_object* v_nextMacroScope_1682_; lean_object* v_ngen_1683_; lean_object* v_auxDeclNGen_1684_; lean_object* v_cache_1685_; lean_object* v_recordedDeps_1686_; lean_object* v_messages_1687_; lean_object* v_infoState_1688_; lean_object* v_snapshotTasks_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1719_; 
v___x_1679_ = lean_st_ref_take(v___y_1671_);
v_traceState_1680_ = lean_ctor_get(v___x_1679_, 4);
v_env_1681_ = lean_ctor_get(v___x_1679_, 0);
v_nextMacroScope_1682_ = lean_ctor_get(v___x_1679_, 1);
v_ngen_1683_ = lean_ctor_get(v___x_1679_, 2);
v_auxDeclNGen_1684_ = lean_ctor_get(v___x_1679_, 3);
v_cache_1685_ = lean_ctor_get(v___x_1679_, 5);
v_recordedDeps_1686_ = lean_ctor_get(v___x_1679_, 6);
v_messages_1687_ = lean_ctor_get(v___x_1679_, 7);
v_infoState_1688_ = lean_ctor_get(v___x_1679_, 8);
v_snapshotTasks_1689_ = lean_ctor_get(v___x_1679_, 9);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1691_ = v___x_1679_;
v_isShared_1692_ = v_isSharedCheck_1719_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_snapshotTasks_1689_);
lean_inc(v_infoState_1688_);
lean_inc(v_messages_1687_);
lean_inc(v_recordedDeps_1686_);
lean_inc(v_cache_1685_);
lean_inc(v_traceState_1680_);
lean_inc(v_auxDeclNGen_1684_);
lean_inc(v_ngen_1683_);
lean_inc(v_nextMacroScope_1682_);
lean_inc(v_env_1681_);
lean_dec(v___x_1679_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1719_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint64_t v_tid_1693_; lean_object* v_traces_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1718_; 
v_tid_1693_ = lean_ctor_get_uint64(v_traceState_1680_, sizeof(void*)*1);
v_traces_1694_ = lean_ctor_get(v_traceState_1680_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_traceState_1680_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1696_ = v_traceState_1680_;
v_isShared_1697_ = v_isSharedCheck_1718_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_traces_1694_);
lean_dec(v_traceState_1680_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1718_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; double v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
v___x_1701_ = 0;
v___x_1702_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
v___x_1703_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1703_, 0, v_cls_1666_);
lean_ctor_set(v___x_1703_, 1, v___x_1699_);
lean_ctor_set(v___x_1703_, 2, v___x_1702_);
lean_ctor_set_float(v___x_1703_, sizeof(void*)*3, v___x_1700_);
lean_ctor_set_float(v___x_1703_, sizeof(void*)*3 + 8, v___x_1700_);
lean_ctor_set_uint8(v___x_1703_, sizeof(void*)*3 + 16, v___x_1701_);
v___x_1704_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2));
v___x_1705_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v_a_1675_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
lean_inc(v_ref_1673_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_ref_1673_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_Lean_PersistentArray_push___redArg(v_traces_1694_, v___x_1706_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1707_);
v___x_1709_ = v___x_1696_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1707_);
lean_ctor_set_uint64(v_reuseFailAlloc_1717_, sizeof(void*)*1, v_tid_1693_);
v___x_1709_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 4, v___x_1709_);
v___x_1711_ = v___x_1691_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_env_1681_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_nextMacroScope_1682_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_ngen_1683_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_auxDeclNGen_1684_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1716_, 5, v_cache_1685_);
lean_ctor_set(v_reuseFailAlloc_1716_, 6, v_recordedDeps_1686_);
lean_ctor_set(v_reuseFailAlloc_1716_, 7, v_messages_1687_);
lean_ctor_set(v_reuseFailAlloc_1716_, 8, v_infoState_1688_);
lean_ctor_set(v_reuseFailAlloc_1716_, 9, v_snapshotTasks_1689_);
v___x_1711_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_st_ref_put(v___y_1671_, v___x_1711_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1698_);
v___x_1714_ = v___x_1677_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1698_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1666_ = stack[0].m_obj;
lean_object* v_msg_1667_ = stack[1].m_obj;
lean_object* v___y_1668_ = stack[2].m_obj;
lean_object* v___y_1669_ = stack[3].m_obj;
lean_object* v___y_1670_ = stack[4].m_obj;
lean_object* v___y_1671_ = stack[5].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* v_cls_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1722_, v_msg_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
v___x_1737_ = l_Lean_MessageData_ofFormat(v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15));
v___x_1757_ = l_Lean_Name_append(v___x_1756_, v___x_1755_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* v_op_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___y_1791_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_f_1947_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; 
v_f_1947_ = l_Lean_Expr_getAppFn(v_op_1778_);
if (lean_obj_tag(v_f_1947_) == 4)
{
lean_object* v_declName_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_declName_2210_ = lean_ctor_get(v_f_1947_, 0);
v___x_2211_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_2211_, v_declName_2210_);
if (v___x_2212_ == 0)
{
v___y_1949_ = v_a_1779_;
v___y_1950_ = v_a_1780_;
v___y_1951_ = v_a_1781_;
v___y_1952_ = v_a_1782_;
v___y_1953_ = v_a_1783_;
v___y_1954_ = v_a_1784_;
v___y_1955_ = v_a_1785_;
v___y_1956_ = v_a_1786_;
v___y_1957_ = v_a_1787_;
v___y_1958_ = v_a_1788_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref_known(v_f_1947_, 2);
lean_dec_ref(v_op_1778_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
else
{
v___y_1949_ = v_a_1779_;
v___y_1950_ = v_a_1780_;
v___y_1951_ = v_a_1781_;
v___y_1952_ = v_a_1782_;
v___y_1953_ = v_a_1783_;
v___y_1954_ = v_a_1784_;
v___y_1955_ = v_a_1785_;
v___y_1956_ = v_a_1786_;
v___y_1957_ = v_a_1787_;
v___y_1958_ = v_a_1788_;
goto v___jp_1948_;
}
v___jp_1790_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1791_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
v___jp_1794_:
{
if (lean_obj_tag(v___y_1795_) == 1)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; 
v_val_1807_ = lean_ctor_get(v___y_1795_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v___y_1795_, 1);
v___x_1808_ = l_Lean_Meta_Grind_AC_mkVar(v_val_1807_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_dec_ref_known(v___x_1808_, 1);
v___y_1791_ = v___y_1796_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v___y_1796_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_dec(v___y_1795_);
v___y_1791_ = v___y_1796_;
goto v___jp_1790_;
}
}
v___jp_1817_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___y_1828_);
lean_ctor_set(v___x_1833_, 1, v___y_1832_);
lean_inc(v___y_1829_);
v___x_1834_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_1829_, v___x_1833_, v___y_1818_, v___y_1825_, v___y_1831_, v___y_1827_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_dec_ref_known(v___x_1834_, 1);
v___y_1795_ = v___y_1824_;
v___y_1796_ = v___y_1830_;
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___y_1822_;
v___y_1799_ = v___y_1819_;
v___y_1800_ = v___y_1823_;
v___y_1801_ = v___y_1820_;
v___y_1802_ = v___y_1821_;
v___y_1803_ = v___y_1818_;
v___y_1804_ = v___y_1825_;
v___y_1805_ = v___y_1831_;
v___y_1806_ = v___y_1827_;
goto v___jp_1794_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v___y_1830_);
lean_dec(v___y_1824_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
v___jp_1843_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_inc_ref(v___y_1858_);
v___x_1859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___y_1858_);
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___y_1849_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
if (lean_obj_tag(v___y_1851_) == 0)
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
v___y_1818_ = v___y_1844_;
v___y_1819_ = v___y_1845_;
v___y_1820_ = v___y_1846_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1850_;
v___y_1824_ = v___y_1851_;
v___y_1825_ = v___y_1852_;
v___y_1826_ = v___y_1853_;
v___y_1827_ = v___y_1854_;
v___y_1828_ = v___x_1863_;
v___y_1829_ = v___y_1855_;
v___y_1830_ = v___y_1857_;
v___y_1831_ = v___y_1856_;
v___y_1832_ = v___x_1864_;
goto v___jp_1817_;
}
else
{
lean_object* v_val_1865_; lean_object* v___x_1866_; 
v_val_1865_ = lean_ctor_get(v___y_1851_, 0);
lean_inc(v_val_1865_);
v___x_1866_ = l_Lean_MessageData_ofExpr(v_val_1865_);
v___y_1818_ = v___y_1844_;
v___y_1819_ = v___y_1845_;
v___y_1820_ = v___y_1846_;
v___y_1821_ = v___y_1847_;
v___y_1822_ = v___y_1848_;
v___y_1823_ = v___y_1850_;
v___y_1824_ = v___y_1851_;
v___y_1825_ = v___y_1852_;
v___y_1826_ = v___y_1853_;
v___y_1827_ = v___y_1854_;
v___y_1828_ = v___x_1863_;
v___y_1829_ = v___y_1855_;
v___y_1830_ = v___y_1857_;
v___y_1831_ = v___y_1856_;
v___y_1832_ = v___x_1866_;
goto v___jp_1817_;
}
}
v___jp_1867_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_inc_ref(v___y_1883_);
v___x_1884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___y_1883_);
v___x_1885_ = l_Lean_MessageData_ofFormat(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___y_1869_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
if (lean_obj_tag(v___y_1870_) == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1844_ = v___y_1868_;
v___y_1845_ = v___y_1871_;
v___y_1846_ = v___y_1872_;
v___y_1847_ = v___y_1873_;
v___y_1848_ = v___y_1874_;
v___y_1849_ = v___x_1888_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1877_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1882_;
v___y_1857_ = v___y_1881_;
v___y_1858_ = v___x_1889_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1890_; 
lean_dec_ref_known(v___y_1870_, 1);
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1844_ = v___y_1868_;
v___y_1845_ = v___y_1871_;
v___y_1846_ = v___y_1872_;
v___y_1847_ = v___y_1873_;
v___y_1848_ = v___y_1874_;
v___y_1849_ = v___x_1888_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1877_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1882_;
v___y_1857_ = v___y_1881_;
v___y_1858_ = v___x_1890_;
goto v___jp_1843_;
}
}
v___jp_1891_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_1901_, v___y_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_structs_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v_structs_1913_ = lean_ctor_get(v_a_1912_, 0);
lean_inc_ref(v_structs_1913_);
lean_dec(v_a_1912_);
v___x_1914_ = lean_array_get_size(v_structs_1913_);
lean_dec_ref(v_structs_1913_);
v___x_1915_ = lean_box(v___y_1893_);
lean_inc(v___y_1894_);
lean_inc(v_snd_1900_);
lean_inc_ref(v_op_1778_);
v___f_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(v___f_1916_, 0, v___x_1914_);
lean_closure_set(v___f_1916_, 1, v___y_1895_);
lean_closure_set(v___f_1916_, 2, v___y_1897_);
lean_closure_set(v___f_1916_, 3, v_op_1778_);
lean_closure_set(v___f_1916_, 4, v_snd_1900_);
lean_closure_set(v___f_1916_, 5, v___y_1896_);
lean_closure_set(v___f_1916_, 6, v___y_1894_);
lean_closure_set(v___f_1916_, 7, v___y_1892_);
lean_closure_set(v___f_1916_, 8, v_fst_1899_);
lean_closure_set(v___f_1916_, 9, v___x_1915_);
v___x_1917_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1918_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1917_, v___f_1916_, v___y_1901_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_toCold_1919_; lean_object* v_options_1920_; uint8_t v_hasTrace_1921_; 
lean_dec_ref_known(v___x_1918_, 1);
v_toCold_1919_ = lean_ctor_get(v___y_1909_, 0);
v_options_1920_ = lean_ctor_get(v_toCold_1919_, 2);
v_hasTrace_1921_ = lean_ctor_get_uint8(v_options_1920_, sizeof(void*)*1);
if (v_hasTrace_1921_ == 0)
{
lean_dec(v___y_1898_);
lean_dec(v___y_1894_);
lean_dec_ref(v_op_1778_);
v___y_1795_ = v_snd_1900_;
v___y_1796_ = v___x_1914_;
v___y_1797_ = v___y_1901_;
v___y_1798_ = v___y_1902_;
v___y_1799_ = v___y_1903_;
v___y_1800_ = v___y_1904_;
v___y_1801_ = v___y_1905_;
v___y_1802_ = v___y_1906_;
v___y_1803_ = v___y_1907_;
v___y_1804_ = v___y_1908_;
v___y_1805_ = v___y_1909_;
v___y_1806_ = v___y_1910_;
goto v___jp_1794_;
}
else
{
lean_object* v_inheritedTraceOptions_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_inheritedTraceOptions_1922_ = lean_ctor_get(v_toCold_1919_, 11);
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
v___x_1925_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1922_, v_options_1920_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_dec(v___y_1898_);
lean_dec(v___y_1894_);
lean_dec_ref(v_op_1778_);
v___y_1795_ = v_snd_1900_;
v___y_1796_ = v___x_1914_;
v___y_1797_ = v___y_1901_;
v___y_1798_ = v___y_1902_;
v___y_1799_ = v___y_1903_;
v___y_1800_ = v___y_1904_;
v___y_1801_ = v___y_1905_;
v___y_1802_ = v___y_1906_;
v___y_1803_ = v___y_1907_;
v___y_1804_ = v___y_1908_;
v___y_1805_ = v___y_1909_;
v___y_1806_ = v___y_1910_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = l_Lean_MessageData_ofExpr(v_op_1778_);
v___x_1927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
if (lean_obj_tag(v___y_1898_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___x_1928_;
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1903_;
v___y_1872_ = v___y_1905_;
v___y_1873_ = v___y_1906_;
v___y_1874_ = v___y_1902_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v_snd_1900_;
v___y_1877_ = v___y_1908_;
v___y_1878_ = v___y_1901_;
v___y_1879_ = v___y_1910_;
v___y_1880_ = v___x_1923_;
v___y_1881_ = v___x_1914_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___x_1929_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1930_; 
lean_dec_ref_known(v___y_1898_, 1);
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1868_ = v___y_1907_;
v___y_1869_ = v___x_1928_;
v___y_1870_ = v___y_1894_;
v___y_1871_ = v___y_1903_;
v___y_1872_ = v___y_1905_;
v___y_1873_ = v___y_1906_;
v___y_1874_ = v___y_1902_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v_snd_1900_;
v___y_1877_ = v___y_1908_;
v___y_1878_ = v___y_1901_;
v___y_1879_ = v___y_1910_;
v___y_1880_ = v___x_1923_;
v___y_1881_ = v___x_1914_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___x_1930_;
goto v___jp_1867_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_snd_1900_);
lean_dec(v___y_1898_);
lean_dec(v___y_1894_);
lean_dec_ref(v_op_1778_);
v_a_1931_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1918_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1918_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_snd_1900_);
lean_dec(v_fst_1899_);
lean_dec(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec(v___y_1892_);
lean_dec_ref(v_op_1778_);
v_a_1939_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1911_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1911_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
v___jp_1948_:
{
lean_object* v___x_1959_; 
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc_ref(v_op_1778_);
v___x_1959_ = lean_infer_type(v_op_1778_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
v___x_1961_ = lean_whnf(v_a_1960_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2193_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2193_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2193_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
if (lean_obj_tag(v_a_1962_) == 7)
{
lean_object* v_binderType_1966_; lean_object* v_body_1967_; uint8_t v___x_1968_; 
v_binderType_1966_ = lean_ctor_get(v_a_1962_, 1);
lean_inc_ref(v_binderType_1966_);
v_body_1967_ = lean_ctor_get(v_a_1962_, 2);
lean_inc_ref(v_body_1967_);
lean_dec_ref_known(v_a_1962_, 3);
v___x_1968_ = l_Lean_Expr_hasLooseBVars(v_body_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1964_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
v___x_1969_ = lean_whnf(v_body_1967_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2176_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2176_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2176_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
if (lean_obj_tag(v_a_1970_) == 7)
{
lean_object* v_binderType_1974_; lean_object* v_body_1975_; uint8_t v___x_1976_; 
v_binderType_1974_ = lean_ctor_get(v_a_1970_, 1);
lean_inc_ref(v_binderType_1974_);
v_body_1975_ = lean_ctor_get(v_a_1970_, 2);
lean_inc_ref(v_body_1975_);
lean_dec_ref_known(v_a_1970_, 3);
v___x_1976_ = l_Lean_Expr_hasLooseBVars(v_body_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_del_object(v___x_1972_);
lean_inc_ref(v_binderType_1966_);
v___x_1977_ = l_Lean_Meta_isExprDefEq(v_binderType_1966_, v_binderType_1974_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2159_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2159_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2159_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec_ref(v_body_1975_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_1983_ = lean_box(0);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1983_);
v___x_1985_ = v___x_1980_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v___x_1987_; 
lean_del_object(v___x_1980_);
lean_inc_ref(v_binderType_1966_);
v___x_1987_ = l_Lean_Meta_isExprDefEq(v_binderType_1966_, v_body_1975_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2150_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2150_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2150_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_1993_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
else
{
lean_object* v___x_1997_; 
lean_del_object(v___x_1990_);
v___x_1997_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___redArg(v_op_1778_, v_f_1947_, v___y_1951_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec_ref(v_f_1947_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2141_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2141_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2141_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_unbox(v_a_1998_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_del_object(v___x_2000_);
lean_inc_ref(v_binderType_1966_);
v___x_2003_ = l_Lean_Meta_getLevel(v_binderType_1966_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc_n(v_a_2004_, 2);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21));
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_a_2004_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
lean_inc_ref(v___x_2007_);
v___x_2008_ = l_Lean_mkConst(v___x_2005_, v___x_2007_);
lean_inc_ref(v_op_1778_);
lean_inc_ref(v_binderType_1966_);
v___x_2009_ = l_Lean_mkAppB(v___x_2008_, v_binderType_1966_, v_op_1778_);
v___x_2010_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2009_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2120_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2120_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2120_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2115_; 
lean_del_object(v___x_2013_);
v_val_2015_ = lean_ctor_get(v_a_2011_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2011_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2017_ = v_a_2011_;
v_isShared_2018_ = v_isSharedCheck_2115_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v_a_2011_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2115_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23));
lean_inc_ref(v___x_2007_);
v___x_2020_ = l_Lean_mkConst(v___x_2019_, v___x_2007_);
lean_inc_ref(v_op_1778_);
lean_inc_ref(v_binderType_1966_);
v___x_2021_ = l_Lean_mkAppB(v___x_2020_, v_binderType_1966_, v_op_1778_);
v___x_2022_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2021_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25));
lean_inc_ref(v___x_2007_);
v___x_2025_ = l_Lean_mkConst(v___x_2024_, v___x_2007_);
lean_inc_ref(v_op_1778_);
lean_inc_ref(v_binderType_1966_);
v___x_2026_ = l_Lean_mkAppB(v___x_2025_, v_binderType_1966_, v_op_1778_);
v___x_2027_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2026_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
lean_inc_ref(v_binderType_1966_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_binderType_1966_);
v___x_2030_ = v___x_2017_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_binderType_1966_);
v___x_2030_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
uint8_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = 0;
v___x_2032_ = lean_box(0);
v___x_2033_ = l_Lean_Meta_mkFreshExprMVar(v___x_2030_, v___x_2031_, v___x_2032_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_n(v_a_2034_, 2);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27));
v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2007_);
lean_inc_ref(v_op_1778_);
lean_inc_ref(v_binderType_1966_);
v___x_2037_ = l_Lean_mkApp3(v___x_2036_, v_binderType_1966_, v_op_1778_, v_a_2034_);
v___x_2038_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2037_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
if (lean_obj_tag(v_a_2039_) == 1)
{
lean_object* v___x_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2079_; 
v___x_2040_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_2034_, v___y_1956_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2079_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2079_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_a_2041_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_1778_, v___y_1949_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = lean_box(0);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc(v___y_1949_);
lean_inc(v_a_2046_);
v___x_2050_ = lean_grind_internalize(v_a_2046_, v_a_2048_, v___x_2049_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref_known(v___x_2050_, 1);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 1);
lean_ctor_set(v___x_2043_, 0, v_a_2046_);
v___x_2052_ = v___x_2043_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2046_);
v___x_2052_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
uint8_t v___x_2053_; 
v___x_2053_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
lean_inc(v_a_2023_);
v___y_1892_ = v_a_2023_;
v___y_1893_ = v___x_2053_;
v___y_1894_ = v_a_2028_;
v___y_1895_ = v_binderType_1966_;
v___y_1896_ = v_val_2015_;
v___y_1897_ = v_a_2004_;
v___y_1898_ = v_a_2023_;
v_fst_1899_ = v_a_2039_;
v_snd_1900_ = v___x_2052_;
v___y_1901_ = v___y_1949_;
v___y_1902_ = v___y_1950_;
v___y_1903_ = v___y_1951_;
v___y_1904_ = v___y_1952_;
v___y_1905_ = v___y_1953_;
v___y_1906_ = v___y_1954_;
v___y_1907_ = v___y_1955_;
v___y_1908_ = v___y_1956_;
v___y_1909_ = v___y_1957_;
v___y_1910_ = v___y_1958_;
goto v___jp_1891_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2046_);
lean_del_object(v___x_2043_);
lean_dec_ref_known(v_a_2039_, 1);
lean_dec(v_a_2028_);
lean_dec(v_a_2023_);
lean_dec(v_val_2015_);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2055_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2050_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2050_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2046_);
lean_del_object(v___x_2043_);
lean_dec_ref_known(v_a_2039_, 1);
lean_dec(v_a_2028_);
lean_dec(v_a_2023_);
lean_dec(v_val_2015_);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2063_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2047_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2047_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2043_);
lean_dec_ref_known(v_a_2039_, 1);
lean_dec(v_a_2028_);
lean_dec(v_a_2023_);
lean_dec(v_val_2015_);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2071_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2045_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2045_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
else
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
lean_dec(v_a_2039_);
lean_dec(v_a_2034_);
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
lean_inc(v_a_2023_);
v___y_1892_ = v_a_2023_;
v___y_1893_ = v___x_2081_;
v___y_1894_ = v_a_2028_;
v___y_1895_ = v_binderType_1966_;
v___y_1896_ = v_val_2015_;
v___y_1897_ = v_a_2004_;
v___y_1898_ = v_a_2023_;
v_fst_1899_ = v___x_2080_;
v_snd_1900_ = v___x_2080_;
v___y_1901_ = v___y_1949_;
v___y_1902_ = v___y_1950_;
v___y_1903_ = v___y_1951_;
v___y_1904_ = v___y_1952_;
v___y_1905_ = v___y_1953_;
v___y_1906_ = v___y_1954_;
v___y_1907_ = v___y_1955_;
v___y_1908_ = v___y_1956_;
v___y_1909_ = v___y_1957_;
v___y_1910_ = v___y_1958_;
goto v___jp_1891_;
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2034_);
lean_dec(v_a_2028_);
lean_dec(v_a_2023_);
lean_dec(v_val_2015_);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2082_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2038_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2038_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_a_2028_);
lean_dec(v_a_2023_);
lean_dec(v_val_2015_);
lean_dec_ref_known(v___x_2007_, 2);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2090_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2033_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2033_);
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
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2023_);
lean_del_object(v___x_2017_);
lean_dec(v_val_2015_);
lean_dec_ref_known(v___x_2007_, 2);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2099_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2027_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2027_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
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
lean_del_object(v___x_2017_);
lean_dec(v_val_2015_);
lean_dec_ref_known(v___x_2007_, 2);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2107_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2022_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2022_);
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
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_a_2011_);
lean_dec_ref_known(v___x_2007_, 2);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v___x_2116_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2116_);
v___x_2118_ = v___x_2013_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref_known(v___x_2007_, 2);
lean_dec(v_a_2004_);
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2121_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2010_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2010_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2129_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2003_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2003_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_dec(v_a_1998_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v___x_2137_ = lean_box(0);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2137_);
v___x_2139_ = v___x_2000_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_op_1778_);
v_a_2142_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_1997_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_1997_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v_a_2151_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_1987_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_1987_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_body_1975_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v_a_2160_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_1977_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_1977_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec_ref(v_body_1975_);
lean_dec_ref(v_binderType_1974_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_2168_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2168_);
v___x_2170_ = v___x_1972_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v_a_1970_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_2172_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2172_);
v___x_2174_ = v___x_1972_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v_a_2177_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_1969_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_1969_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec_ref(v_body_1967_);
lean_dec_ref(v_binderType_1966_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_2185_ = lean_box(0);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_2185_);
v___x_2187_ = v___x_1964_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec(v_a_1962_);
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v___x_2189_ = lean_box(0);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_2189_);
v___x_2191_ = v___x_1964_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v_a_2194_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_1961_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_1961_);
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
lean_dec_ref(v_f_1947_);
lean_dec_ref(v_op_1778_);
v_a_2202_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_1959_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_1959_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_1778_ = stack[0].m_obj;
lean_object* v_a_1779_ = stack[1].m_obj;
lean_object* v_a_1780_ = stack[2].m_obj;
lean_object* v_a_1781_ = stack[3].m_obj;
lean_object* v_a_1782_ = stack[4].m_obj;
lean_object* v_a_1783_ = stack[5].m_obj;
lean_object* v_a_1784_ = stack[6].m_obj;
lean_object* v_a_1785_ = stack[7].m_obj;
lean_object* v_a_1786_ = stack[8].m_obj;
lean_object* v_a_1787_ = stack[9].m_obj;
lean_object* v_a_1788_ = stack[10].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* v_op_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec(v_a_2217_);
return v_res_2228_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* v_cls_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_2229_, v_msg_2230_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2229_ = stack[0].m_obj;
lean_object* v_msg_2230_ = stack[1].m_obj;
lean_object* v___y_2231_ = stack[2].m_obj;
lean_object* v___y_2232_ = stack[3].m_obj;
lean_object* v___y_2233_ = stack[4].m_obj;
lean_object* v___y_2234_ = stack[5].m_obj;
lean_object* v___y_2235_ = stack[6].m_obj;
lean_object* v___y_2236_ = stack[7].m_obj;
lean_object* v___y_2237_ = stack[8].m_obj;
lean_object* v___y_2238_ = stack[9].m_obj;
lean_object* v___y_2239_ = stack[10].m_obj;
lean_object* v___y_2240_ = stack[11].m_obj;
lean_object* v_res_2243_;
v_res_2243_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2229_, v_msg_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
stack->m_obj
 = v_res_2243_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* v_cls_2244_, lean_object* v_msg_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2244_, v_msg_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec(v___y_2246_);
return v_res_2257_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* v_00_u03b2_2258_, lean_object* v_m_2259_, lean_object* v_a_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_2259_, v_a_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2259_ = stack[1].m_obj;
lean_object* v_a_2260_ = stack[2].m_obj;
uint8_t v_res_2262_;
v_res_2262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_box(0), v_m_2259_, v_a_2260_);
stack->m_num = v_res_2262_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_2263_, lean_object* v_m_2264_, lean_object* v_a_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_2263_, v_m_2264_, v_a_2265_);
lean_dec(v_a_2265_);
lean_dec_ref(v_m_2264_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* v_op_2268_, lean_object* v_a_2269_, lean_object* v_s_2270_){
_start:
{
lean_object* v_structs_2271_; lean_object* v_opIdOf_2272_; lean_object* v_exprToOpIds_2273_; lean_object* v_steps_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_structs_2271_ = lean_ctor_get(v_s_2270_, 0);
v_opIdOf_2272_ = lean_ctor_get(v_s_2270_, 1);
v_exprToOpIds_2273_ = lean_ctor_get(v_s_2270_, 2);
v_steps_2274_ = lean_ctor_get(v_s_2270_, 3);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_s_2270_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v_s_2270_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_steps_2274_);
lean_inc(v_exprToOpIds_2273_);
lean_inc(v_opIdOf_2272_);
lean_inc(v_structs_2271_);
lean_dec(v_s_2270_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_2272_, v_op_2268_, v_a_2269_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_structs_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_exprToOpIds_2273_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_steps_2274_);
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
lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* v_op_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2284_, v_a_2292_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2327_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2327_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2327_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_opIdOf_2300_; lean_object* v___x_2301_; 
v_opIdOf_2300_ = lean_ctor_get(v_a_2296_, 1);
lean_inc_ref(v_opIdOf_2300_);
lean_dec(v_a_2296_);
v___x_2301_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_2300_, v_op_2283_);
lean_dec_ref(v_opIdOf_2300_);
if (lean_obj_tag(v___x_2301_) == 1)
{
lean_object* v_val_2302_; lean_object* v___x_2304_; 
lean_dec_ref(v_op_2283_);
v_val_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v___x_2301_, 1);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_val_2302_);
v___x_2304_ = v___x_2298_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_val_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
else
{
lean_object* v___x_2306_; 
lean_dec(v___x_2301_);
lean_del_object(v___x_2298_);
lean_inc_ref(v_op_2283_);
v___x_2306_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc_n(v_a_2307_, 2);
lean_dec_ref_known(v___x_2306_, 1);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2308_, 0, v_op_2283_);
lean_closure_set(v___f_2308_, 1, v_a_2307_);
v___x_2309_ = l_Lean_Meta_Grind_AC_acExt;
v___x_2310_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2309_, v___f_2308_, v_a_2284_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2310_, 0);
lean_dec(v_unused_2318_);
v___x_2312_ = v___x_2310_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v___x_2310_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_a_2307_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2307_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_a_2307_);
v_a_2319_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2310_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2310_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_dec_ref(v_op_2283_);
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec_ref(v_op_2283_);
v_a_2328_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2295_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2295_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_getOpId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2283_ = stack[0].m_obj;
lean_object* v_a_2284_ = stack[1].m_obj;
lean_object* v_a_2285_ = stack[2].m_obj;
lean_object* v_a_2286_ = stack[3].m_obj;
lean_object* v_a_2287_ = stack[4].m_obj;
lean_object* v_a_2288_ = stack[5].m_obj;
lean_object* v_a_2289_ = stack[6].m_obj;
lean_object* v_a_2290_ = stack[7].m_obj;
lean_object* v_a_2291_ = stack[8].m_obj;
lean_object* v_a_2292_ = stack[9].m_obj;
lean_object* v_a_2293_ = stack[10].m_obj;
lean_object* v_res_2336_;
v_res_2336_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
stack->m_obj
 = v_res_2336_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* v_op_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec(v_a_2338_);
return v_res_2349_;
}
}
lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* v_e_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
uint8_t v___y_2364_; uint8_t v___x_2397_; 
v___x_2397_ = l_Lean_Expr_isApp(v_e_2350_);
if (v___x_2397_ == 0)
{
v___y_2364_ = v___x_2397_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = l_Lean_Expr_appFn_x21(v_e_2350_);
v___x_2399_ = l_Lean_Expr_isApp(v___x_2398_);
lean_dec_ref(v___x_2398_);
v___y_2364_ = v___x_2399_;
goto v___jp_2363_;
}
v___jp_2363_:
{
if (v___y_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
else
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Meta_Grind_AC_getOp(v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2388_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2388_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2388_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2372_ = l_Lean_Expr_appFn_x21(v_e_2350_);
v___x_2373_ = l_Lean_Expr_appFn_x21(v___x_2372_);
v___x_2374_ = lean_ptr_addr(v___x_2373_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = lean_ptr_addr(v_a_2368_);
lean_dec(v_a_2368_);
v___x_2376_ = lean_usize_dec_eq(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_dec_ref(v___x_2372_);
v___x_2377_ = lean_box(0);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2377_);
v___x_2379_ = v___x_2370_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2381_ = l_Lean_Expr_appArg_x21(v___x_2372_);
lean_dec_ref(v___x_2372_);
v___x_2382_ = l_Lean_Expr_appArg_x21(v_e_2350_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2384_);
v___x_2386_ = v___x_2370_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
v_a_2389_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2367_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2367_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_isOp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2350_ = stack[0].m_obj;
lean_object* v_a_2351_ = stack[1].m_obj;
lean_object* v_a_2352_ = stack[2].m_obj;
lean_object* v_a_2353_ = stack[3].m_obj;
lean_object* v_a_2354_ = stack[4].m_obj;
lean_object* v_a_2355_ = stack[5].m_obj;
lean_object* v_a_2356_ = stack[6].m_obj;
lean_object* v_a_2357_ = stack[7].m_obj;
lean_object* v_a_2358_ = stack[8].m_obj;
lean_object* v_a_2359_ = stack[9].m_obj;
lean_object* v_a_2360_ = stack[10].m_obj;
lean_object* v_a_2361_ = stack[11].m_obj;
lean_object* v_res_2400_;
v_res_2400_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
stack->m_obj
 = v_res_2400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* v_e_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_e_2401_);
return v_res_2414_;
}
}
lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2443_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2443_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2443_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v_commInst_x3f_2432_; 
v_commInst_x3f_2432_ = lean_ctor_get(v_a_2428_, 7);
lean_inc(v_commInst_x3f_2432_);
lean_dec(v_a_2428_);
if (lean_obj_tag(v_commInst_x3f_2432_) == 0)
{
uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = 0;
v___x_2434_ = lean_box(v___x_2433_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2434_);
v___x_2436_ = v___x_2430_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
else
{
uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_dec_ref_known(v_commInst_x3f_2432_, 1);
v___x_2438_ = 1;
v___x_2439_ = lean_box(v___x_2438_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2439_);
v___x_2441_ = v___x_2430_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
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
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2427_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2427_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_isCommutative_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2415_ = stack[0].m_obj;
lean_object* v_a_2416_ = stack[1].m_obj;
lean_object* v_a_2417_ = stack[2].m_obj;
lean_object* v_a_2418_ = stack[3].m_obj;
lean_object* v_a_2419_ = stack[4].m_obj;
lean_object* v_a_2420_ = stack[5].m_obj;
lean_object* v_a_2421_ = stack[6].m_obj;
lean_object* v_a_2422_ = stack[7].m_obj;
lean_object* v_a_2423_ = stack[8].m_obj;
lean_object* v_a_2424_ = stack[9].m_obj;
lean_object* v_a_2425_ = stack[10].m_obj;
lean_object* v_res_2452_;
v_res_2452_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
stack->m_obj
 = v_res_2452_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
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
lean_dec(v_a_2453_);
return v_res_2465_;
}
}
lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2494_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2494_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2494_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_neutralInst_x3f_2483_; 
v_neutralInst_x3f_2483_ = lean_ctor_get(v_a_2479_, 8);
lean_inc(v_neutralInst_x3f_2483_);
lean_dec(v_a_2479_);
if (lean_obj_tag(v_neutralInst_x3f_2483_) == 0)
{
uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = 0;
v___x_2485_ = lean_box(v___x_2484_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2485_);
v___x_2487_ = v___x_2481_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
else
{
uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_dec_ref_known(v_neutralInst_x3f_2483_, 1);
v___x_2489_ = 1;
v___x_2490_ = lean_box(v___x_2489_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2490_);
v___x_2492_ = v___x_2481_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2478_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2478_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_hasNeutral_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2466_ = stack[0].m_obj;
lean_object* v_a_2467_ = stack[1].m_obj;
lean_object* v_a_2468_ = stack[2].m_obj;
lean_object* v_a_2469_ = stack[3].m_obj;
lean_object* v_a_2470_ = stack[4].m_obj;
lean_object* v_a_2471_ = stack[5].m_obj;
lean_object* v_a_2472_ = stack[6].m_obj;
lean_object* v_a_2473_ = stack[7].m_obj;
lean_object* v_a_2474_ = stack[8].m_obj;
lean_object* v_a_2475_ = stack[9].m_obj;
lean_object* v_a_2476_ = stack[10].m_obj;
lean_object* v_res_2503_;
v_res_2503_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
stack->m_obj
 = v_res_2503_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec(v_a_2504_);
return v_res_2516_;
}
}
lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2545_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2545_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2545_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_idempotentInst_x3f_2534_; 
v_idempotentInst_x3f_2534_ = lean_ctor_get(v_a_2530_, 6);
lean_inc(v_idempotentInst_x3f_2534_);
lean_dec(v_a_2530_);
if (lean_obj_tag(v_idempotentInst_x3f_2534_) == 0)
{
uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2535_ = 0;
v___x_2536_ = lean_box(v___x_2535_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2536_);
v___x_2538_ = v___x_2532_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_dec_ref_known(v_idempotentInst_x3f_2534_, 1);
v___x_2540_ = 1;
v___x_2541_ = lean_box(v___x_2540_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2541_);
v___x_2543_ = v___x_2532_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_a_2546_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2529_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2529_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_AC_isIdempotent_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2517_ = stack[0].m_obj;
lean_object* v_a_2518_ = stack[1].m_obj;
lean_object* v_a_2519_ = stack[2].m_obj;
lean_object* v_a_2520_ = stack[3].m_obj;
lean_object* v_a_2521_ = stack[4].m_obj;
lean_object* v_a_2522_ = stack[5].m_obj;
lean_object* v_a_2523_ = stack[6].m_obj;
lean_object* v_a_2524_ = stack[7].m_obj;
lean_object* v_a_2525_ = stack[8].m_obj;
lean_object* v_a_2526_ = stack[9].m_obj;
lean_object* v_a_2527_ = stack[10].m_obj;
lean_object* v_res_2554_;
v_res_2554_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec(v_a_2555_);
return v_res_2567_;
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
