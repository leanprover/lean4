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
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
return v_x_519_;
}
else
{
lean_object* v_key_521_; lean_object* v_value_522_; lean_object* v_tail_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_549_; 
v_key_521_ = lean_ctor_get(v_x_520_, 0);
v_value_522_ = lean_ctor_get(v_x_520_, 1);
v_tail_523_ = lean_ctor_get(v_x_520_, 2);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_520_);
if (v_isSharedCheck_549_ == 0)
{
v___x_525_ = v_x_520_;
v_isShared_526_ = v_isSharedCheck_549_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_tail_523_);
lean_inc(v_value_522_);
lean_inc(v_key_521_);
lean_dec(v_x_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_549_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; uint64_t v___y_529_; 
v___x_527_ = lean_array_get_size(v_x_519_);
if (lean_obj_tag(v_key_521_) == 0)
{
uint64_t v___x_547_; 
v___x_547_ = 1723ULL;
v___y_529_ = v___x_547_;
goto v___jp_528_;
}
else
{
uint64_t v_hash_548_; 
v_hash_548_ = lean_ctor_get_uint64(v_key_521_, sizeof(void*)*2);
v___y_529_ = v_hash_548_;
goto v___jp_528_;
}
v___jp_528_:
{
uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v_fold_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_530_ = 32ULL;
v___x_531_ = lean_uint64_shift_right(v___y_529_, v___x_530_);
v_fold_532_ = lean_uint64_xor(v___y_529_, v___x_531_);
v___x_533_ = 16ULL;
v___x_534_ = lean_uint64_shift_right(v_fold_532_, v___x_533_);
v___x_535_ = lean_uint64_xor(v_fold_532_, v___x_534_);
v___x_536_ = lean_uint64_to_usize(v___x_535_);
v___x_537_ = lean_usize_of_nat(v___x_527_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_sub(v___x_537_, v___x_538_);
v___x_540_ = lean_usize_land(v___x_536_, v___x_539_);
v___x_541_ = lean_array_uget_borrowed(v_x_519_, v___x_540_);
lean_inc(v___x_541_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 2, v___x_541_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_key_521_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_value_522_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v___x_541_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_array_uset(v_x_519_, v___x_540_, v___x_543_);
v_x_519_ = v___x_544_;
v_x_520_ = v_tail_523_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_550_, lean_object* v_source_551_, lean_object* v_target_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_array_get_size(v_source_551_);
v___x_554_ = lean_nat_dec_lt(v_i_550_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec_ref(v_source_551_);
lean_dec(v_i_550_);
return v_target_552_;
}
else
{
lean_object* v_es_555_; lean_object* v___x_556_; lean_object* v_source_557_; lean_object* v_target_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_es_555_ = lean_array_fget(v_source_551_, v_i_550_);
v___x_556_ = lean_box(0);
v_source_557_ = lean_array_fset(v_source_551_, v_i_550_, v___x_556_);
v_target_558_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_552_, v_es_555_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_i_550_, v___x_559_);
lean_dec(v_i_550_);
v_i_550_ = v___x_560_;
v_source_551_ = v_source_557_;
v_target_552_ = v_target_558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(lean_object* v_data_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_nbuckets_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_563_ = lean_array_get_size(v_data_562_);
v___x_564_ = lean_unsigned_to_nat(2u);
v_nbuckets_565_ = lean_nat_mul(v___x_563_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_box(0);
v___x_568_ = lean_mk_array(v_nbuckets_565_, v___x_567_);
v___x_569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_566_, v_data_562_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(lean_object* v_a_570_, lean_object* v_x_571_){
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
v___x_575_ = lean_name_eq(v_key_573_, v_a_570_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_577_, lean_object* v_x_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_577_, v_x_578_);
lean_dec(v_x_578_);
lean_dec(v_a_577_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(lean_object* v_m_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_size_584_; lean_object* v_buckets_585_; lean_object* v___x_586_; uint64_t v___y_588_; 
v_size_584_ = lean_ctor_get(v_m_581_, 0);
v_buckets_585_ = lean_ctor_get(v_m_581_, 1);
v___x_586_ = lean_array_get_size(v_buckets_585_);
if (lean_obj_tag(v_a_582_) == 0)
{
uint64_t v___x_625_; 
v___x_625_ = 1723ULL;
v___y_588_ = v___x_625_;
goto v___jp_587_;
}
else
{
uint64_t v_hash_626_; 
v_hash_626_ = lean_ctor_get_uint64(v_a_582_, sizeof(void*)*2);
v___y_588_ = v_hash_626_;
goto v___jp_587_;
}
v___jp_587_:
{
uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v_fold_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v___x_599_; lean_object* v_bkt_600_; uint8_t v___x_601_; 
v___x_589_ = 32ULL;
v___x_590_ = lean_uint64_shift_right(v___y_588_, v___x_589_);
v_fold_591_ = lean_uint64_xor(v___y_588_, v___x_590_);
v___x_592_ = 16ULL;
v___x_593_ = lean_uint64_shift_right(v_fold_591_, v___x_592_);
v___x_594_ = lean_uint64_xor(v_fold_591_, v___x_593_);
v___x_595_ = lean_uint64_to_usize(v___x_594_);
v___x_596_ = lean_usize_of_nat(v___x_586_);
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_sub(v___x_596_, v___x_597_);
v___x_599_ = lean_usize_land(v___x_595_, v___x_598_);
v_bkt_600_ = lean_array_uget_borrowed(v_buckets_585_, v___x_599_);
v___x_601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_582_, v_bkt_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_622_; 
lean_inc_ref(v_buckets_585_);
lean_inc(v_size_584_);
v_isSharedCheck_622_ = !lean_is_exclusive(v_m_581_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_623_ = lean_ctor_get(v_m_581_, 1);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_m_581_, 0);
lean_dec(v_unused_624_);
v___x_603_ = v_m_581_;
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_m_581_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_622_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v_size_x27_606_; lean_object* v___x_607_; lean_object* v_buckets_x27_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v_size_x27_606_ = lean_nat_add(v_size_584_, v___x_605_);
lean_dec(v_size_584_);
lean_inc(v_bkt_600_);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v_a_582_);
lean_ctor_set(v___x_607_, 1, v_b_583_);
lean_ctor_set(v___x_607_, 2, v_bkt_600_);
v_buckets_x27_608_ = lean_array_uset(v_buckets_585_, v___x_599_, v___x_607_);
v___x_609_ = lean_unsigned_to_nat(4u);
v___x_610_ = lean_nat_mul(v_size_x27_606_, v___x_609_);
v___x_611_ = lean_unsigned_to_nat(3u);
v___x_612_ = lean_nat_div(v___x_610_, v___x_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_array_get_size(v_buckets_x27_608_);
v___x_614_ = lean_nat_dec_le(v___x_612_, v___x_613_);
lean_dec(v___x_612_);
if (v___x_614_ == 0)
{
lean_object* v_val_615_; lean_object* v___x_617_; 
v_val_615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_buckets_x27_608_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_val_615_);
lean_ctor_set(v___x_603_, 0, v_size_x27_606_);
v___x_617_ = v___x_603_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_size_x27_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_val_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v___x_620_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_buckets_x27_608_);
lean_ctor_set(v___x_603_, 0, v_size_x27_606_);
v___x_620_ = v___x_603_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_size_x27_606_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_buckets_x27_608_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_dec(v_b_583_);
lean_dec(v_a_582_);
return v_m_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(lean_object* v_as_x27_627_, lean_object* v_b_628_){
_start:
{
if (lean_obj_tag(v_as_x27_627_) == 0)
{
return v_b_628_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; lean_object* v_r_632_; 
v_head_629_ = lean_ctor_get(v_as_x27_627_, 0);
v_tail_630_ = lean_ctor_get(v_as_x27_627_, 1);
v___x_631_ = lean_box(0);
lean_inc(v_head_629_);
v_r_632_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_628_, v_head_629_, v___x_631_);
v_as_x27_627_ = v_tail_630_;
v_b_628_ = v_r_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_634_, lean_object* v_b_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_634_, v_b_635_);
lean_dec(v_as_x27_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(lean_object* v_m_637_, lean_object* v_l_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_l_638_, v_m_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(lean_object* v_m_640_, lean_object* v_l_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_640_, v_l_641_);
lean_dec(v_l_641_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
v___x_718_ = lean_unsigned_to_nat(16u);
v___x_719_ = lean_mk_array(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36));
v___x_725_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v___x_724_, v___x_723_);
return v___x_725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(lean_object* v_00_u03b2_727_, lean_object* v_m_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_728_, v_a_729_, v_b_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(lean_object* v_as_732_, lean_object* v_as_x27_733_, lean_object* v_b_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_733_, v_b_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(lean_object* v_as_737_, lean_object* v_as_x27_738_, lean_object* v_b_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_as_737_, v_as_x27_738_, v_b_739_, v_a_740_);
lean_dec(v_as_x27_738_);
lean_dec(v_as_737_);
return v_res_741_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_742_, lean_object* v_a_743_, lean_object* v_x_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_746_, lean_object* v_a_747_, lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_746_, v_a_747_, v_x_748_);
lean_dec(v_x_748_);
lean_dec(v_a_747_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_751_, lean_object* v_data_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_data_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_754_, lean_object* v_i_755_, lean_object* v_source_756_, lean_object* v_target_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v_i_755_, v_source_756_, v_target_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(lean_object* v_op_788_, lean_object* v_f_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_792_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_877_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_877_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_877_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_877_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v_ring_810_; uint8_t v___y_812_; lean_object* v___y_813_; 
v_ring_810_ = lean_ctor_get_uint8(v_a_806_, sizeof(void*)*14 + 21);
lean_dec(v_a_806_);
if (v_ring_810_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_box(v_ring_810_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_857_);
v___x_859_ = v___x_808_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
if (lean_obj_tag(v_f_789_) == 4)
{
lean_object* v_declName_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
lean_del_object(v___x_808_);
v_declName_861_ = lean_ctor_get(v_f_789_, 0);
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2));
v___x_863_ = lean_name_eq(v_declName_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5));
v___x_865_ = lean_name_eq(v_declName_861_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8));
v___x_867_ = lean_name_eq(v_declName_861_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11));
v___x_869_ = lean_name_eq(v_declName_861_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14));
v___x_871_ = lean_name_eq(v_declName_861_, v___x_870_);
if (v___x_871_ == 0)
{
goto v___jp_801_;
}
else
{
goto v___jp_832_;
}
}
else
{
goto v___jp_832_;
}
}
else
{
goto v___jp_832_;
}
}
else
{
goto v___jp_832_;
}
}
else
{
goto v___jp_832_;
}
}
else
{
uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = 0;
v___x_873_ = lean_box(v___x_872_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_873_);
v___x_875_ = v___x_808_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
v___jp_811_:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v___y_813_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_823_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
if (lean_obj_tag(v_a_815_) == 0)
{
lean_del_object(v___x_817_);
goto v___jp_801_;
}
else
{
lean_dec_ref_known(v_a_815_, 1);
if (v___y_812_ == 0)
{
lean_del_object(v___x_817_);
goto v___jp_801_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_box(v_ring_810_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_814_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_814_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
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
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = l_Lean_Expr_getAppNumArgs(v_op_788_);
v___x_834_ = lean_unsigned_to_nat(4u);
v___x_835_ = lean_nat_dec_eq(v___x_833_, v___x_834_);
lean_dec(v___x_833_);
if (v___x_835_ == 0)
{
goto v___jp_801_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = l_Lean_Expr_appFn_x21(v_op_788_);
v___x_837_ = l_Lean_Expr_appFn_x21(v___x_836_);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Lean_Expr_appArg_x21(v___x_837_);
lean_dec_ref(v___x_837_);
lean_inc_ref(v___x_838_);
v___x_839_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v___x_838_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_a_840_) == 0)
{
lean_del_object(v___x_842_);
v___y_812_ = v___x_835_;
v___y_813_ = v___x_838_;
goto v___jp_811_;
}
else
{
lean_dec_ref_known(v_a_840_, 1);
if (v___x_835_ == 0)
{
lean_del_object(v___x_842_);
v___y_812_ = v___x_835_;
v___y_813_ = v___x_838_;
goto v___jp_811_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_846_; 
lean_dec_ref(v___x_838_);
v___x_844_ = lean_box(v_ring_810_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_838_);
v_a_849_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_839_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_839_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_805_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_805_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
v___jp_801_:
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = 0;
v___x_803_ = lean_box(v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(lean_object* v_op_886_, lean_object* v_f_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_886_, v_f_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_f_887_);
lean_dec_ref(v_op_886_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_i_902_, lean_object* v_k_903_){
_start:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_array_get_size(v_keys_900_);
v___x_905_ = lean_nat_dec_lt(v_i_902_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec(v_i_902_);
v___x_906_ = lean_box(0);
return v___x_906_;
}
else
{
lean_object* v_k_x27_907_; size_t v___x_908_; size_t v___x_909_; uint8_t v___x_910_; 
v_k_x27_907_ = lean_array_fget_borrowed(v_keys_900_, v_i_902_);
v___x_908_ = lean_ptr_addr(v_k_903_);
v___x_909_ = lean_ptr_addr(v_k_x27_907_);
v___x_910_ = lean_usize_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_902_, v___x_911_);
lean_dec(v_i_902_);
v_i_902_ = v___x_912_;
goto _start;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_array_fget_borrowed(v_vals_901_, v_i_902_);
lean_dec(v_i_902_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(lean_object* v_x_921_, size_t v_x_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_921_) == 0)
{
lean_object* v_es_924_; lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v_j_928_; lean_object* v___x_929_; 
v_es_924_ = lean_ctor_get(v_x_921_, 0);
v___x_925_ = lean_box(2);
v___x_926_ = ((size_t)31ULL);
v___x_927_ = lean_usize_land(v_x_922_, v___x_926_);
v_j_928_ = lean_usize_to_nat(v___x_927_);
v___x_929_ = lean_array_get_borrowed(v___x_925_, v_es_924_, v_j_928_);
lean_dec(v_j_928_);
switch(lean_obj_tag(v___x_929_))
{
case 0:
{
lean_object* v_key_930_; lean_object* v_val_931_; size_t v___x_932_; size_t v___x_933_; uint8_t v___x_934_; 
v_key_930_ = lean_ctor_get(v___x_929_, 0);
v_val_931_ = lean_ctor_get(v___x_929_, 1);
v___x_932_ = lean_ptr_addr(v_x_923_);
v___x_933_ = lean_ptr_addr(v_key_930_);
v___x_934_ = lean_usize_dec_eq(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_box(0);
return v___x_935_;
}
else
{
lean_object* v___x_936_; 
lean_inc(v_val_931_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v_val_931_);
return v___x_936_;
}
}
case 1:
{
lean_object* v_node_937_; size_t v___x_938_; size_t v___x_939_; 
v_node_937_ = lean_ctor_get(v___x_929_, 0);
v___x_938_ = ((size_t)5ULL);
v___x_939_ = lean_usize_shift_right(v_x_922_, v___x_938_);
v_x_921_ = v_node_937_;
v_x_922_ = v___x_939_;
goto _start;
}
default: 
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
return v___x_941_;
}
}
}
else
{
lean_object* v_ks_942_; lean_object* v_vs_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_ks_942_ = lean_ctor_get(v_x_921_, 0);
v_vs_943_ = lean_ctor_get(v_x_921_, 1);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_942_, v_vs_943_, v___x_944_, v_x_923_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
size_t v_x_972__boxed_949_; lean_object* v_res_950_; 
v_x_972__boxed_949_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_res_950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_946_, v_x_972__boxed_949_, v_x_948_);
lean_dec_ref(v_x_948_);
lean_dec_ref(v_x_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; uint64_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_953_ = lean_ptr_addr(v_x_952_);
v___x_954_ = ((size_t)3ULL);
v___x_955_ = lean_usize_shift_right(v___x_953_, v___x_954_);
v___x_956_ = lean_usize_to_uint64(v___x_955_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_951_, v___x_957_, v_x_952_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_959_, v_x_960_);
lean_dec_ref(v_x_960_);
lean_dec_ref(v_x_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg(lean_object* v_e_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_981_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_exprToOpIds_971_; lean_object* v___x_972_; 
v_exprToOpIds_971_ = lean_ctor_get(v_a_967_, 2);
lean_inc_ref(v_exprToOpIds_971_);
lean_dec(v_a_967_);
v___x_972_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_971_, v_e_962_);
lean_dec_ref(v_exprToOpIds_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; 
v_val_977_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v___x_972_, 1);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_val_977_);
v___x_979_ = v___x_969_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_val_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_966_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_966_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(lean_object* v_e_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_990_, v_a_991_, v_a_992_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_990_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds(lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_995_, v_a_996_, v_a_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getTermOpIds___boxed(lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Meta_Grind_AC_getTermOpIds(v_e_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_e_1008_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_x_1022_, v_x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(v_00_u03b2_1025_, v_x_1026_, v_x_1027_);
lean_dec_ref(v_x_1027_);
lean_dec_ref(v_x_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, size_t v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_1030_, v_x_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
size_t v_x_1103__boxed_1038_; lean_object* v_res_1039_; 
v_x_1103__boxed_1038_ = lean_unbox_usize(v_x_1036_);
lean_dec(v_x_1036_);
v_res_1039_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_1034_, v_x_1035_, v_x_1103__boxed_1038_, v_x_1037_);
lean_dec_ref(v_x_1037_);
lean_dec_ref(v_x_1035_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1040_, lean_object* v_keys_1041_, lean_object* v_vals_1042_, lean_object* v_heq_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_1041_, v_vals_1042_, v_i_1044_, v_k_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1047_, lean_object* v_keys_1048_, lean_object* v_vals_1049_, lean_object* v_heq_1050_, lean_object* v_i_1051_, lean_object* v_k_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_1047_, v_keys_1048_, v_vals_1049_, v_heq_1050_, v_i_1051_, v_k_1052_);
lean_dec_ref(v_k_1052_);
lean_dec_ref(v_vals_1049_);
lean_dec_ref(v_keys_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(lean_object* v_opId_1054_, lean_object* v_a_1055_){
_start:
{
if (lean_obj_tag(v_a_1055_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_opId_1054_);
lean_ctor_set(v___x_1056_, 1, v_a_1055_);
return v___x_1056_;
}
else
{
lean_object* v_head_1057_; lean_object* v_tail_1058_; uint8_t v___x_1059_; 
v_head_1057_ = lean_ctor_get(v_a_1055_, 0);
v_tail_1058_ = lean_ctor_get(v_a_1055_, 1);
v___x_1059_ = lean_nat_dec_lt(v_opId_1054_, v_head_1057_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1071_; 
lean_inc(v_tail_1058_);
lean_inc(v_head_1057_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; lean_object* v_unused_1073_; 
v_unused_1072_ = lean_ctor_get(v_a_1055_, 1);
lean_dec(v_unused_1072_);
v_unused_1073_ = lean_ctor_get(v_a_1055_, 0);
lean_dec(v_unused_1073_);
v___x_1061_ = v_a_1055_;
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_a_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_eq(v_opId_1054_, v_head_1057_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1054_, v_tail_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1064_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_head_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1069_; 
lean_dec(v_head_1057_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_opId_1054_);
v___x_1069_ = v___x_1061_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_opId_1054_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_tail_1058_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_opId_1054_);
lean_ctor_set(v___x_1074_, 1, v_a_1055_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v_ks_1079_; lean_object* v_vs_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1106_; 
v_ks_1079_ = lean_ctor_get(v_x_1075_, 0);
v_vs_1080_ = lean_ctor_get(v_x_1075_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1082_ = v_x_1075_;
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_vs_1080_);
lean_inc(v_ks_1079_);
lean_dec(v_x_1075_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_array_get_size(v_ks_1079_);
v___x_1085_ = lean_nat_dec_lt(v_x_1076_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_dec(v_x_1076_);
v___x_1086_ = lean_array_push(v_ks_1079_, v_x_1077_);
v___x_1087_ = lean_array_push(v_vs_1080_, v_x_1078_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1087_);
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v_k_x27_1091_; size_t v___x_1092_; size_t v___x_1093_; uint8_t v___x_1094_; 
v_k_x27_1091_ = lean_array_fget_borrowed(v_ks_1079_, v_x_1076_);
v___x_1092_ = lean_ptr_addr(v_x_1077_);
v___x_1093_ = lean_ptr_addr(v_k_x27_1091_);
v___x_1094_ = lean_usize_dec_eq(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1096_; 
if (v_isShared_1083_ == 0)
{
v___x_1096_ = v___x_1082_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_ks_1079_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_vs_1080_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(1u);
v___x_1098_ = lean_nat_add(v_x_1076_, v___x_1097_);
lean_dec(v_x_1076_);
v_x_1075_ = v___x_1096_;
v_x_1076_ = v___x_1098_;
goto _start;
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1101_ = lean_array_fset(v_ks_1079_, v_x_1076_, v_x_1077_);
v___x_1102_ = lean_array_fset(v_vs_1080_, v_x_1076_, v_x_1078_);
lean_dec(v_x_1076_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1102_);
lean_ctor_set(v___x_1082_, 0, v___x_1101_);
v___x_1104_ = v___x_1082_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1107_, lean_object* v_k_1108_, lean_object* v_v_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1107_, v___x_1110_, v_k_1108_, v_v_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(lean_object* v_x_1113_, size_t v_x_1114_, size_t v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
lean_object* v_es_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v_j_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_es_1118_ = lean_ctor_get(v_x_1113_, 0);
v___x_1119_ = ((size_t)31ULL);
v___x_1120_ = lean_usize_land(v_x_1114_, v___x_1119_);
v_j_1121_ = lean_usize_to_nat(v___x_1120_);
v___x_1122_ = lean_array_get_size(v_es_1118_);
v___x_1123_ = lean_nat_dec_lt(v_j_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec(v_j_1121_);
lean_dec(v_x_1117_);
lean_dec_ref(v_x_1116_);
return v_x_1113_;
}
else
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1164_; 
lean_inc_ref(v_es_1118_);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_x_1113_, 0);
lean_dec(v_unused_1165_);
v___x_1125_ = v_x_1113_;
v_isShared_1126_ = v_isSharedCheck_1164_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_x_1113_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1164_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_v_1127_; lean_object* v___x_1128_; lean_object* v_xs_x27_1129_; lean_object* v___y_1131_; 
v_v_1127_ = lean_array_fget(v_es_1118_, v_j_1121_);
v___x_1128_ = lean_box(0);
v_xs_x27_1129_ = lean_array_fset(v_es_1118_, v_j_1121_, v___x_1128_);
switch(lean_obj_tag(v_v_1127_))
{
case 0:
{
lean_object* v_key_1136_; lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1149_; 
v_key_1136_ = lean_ctor_get(v_v_1127_, 0);
v_val_1137_ = lean_ctor_get(v_v_1127_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_v_1127_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1139_ = v_v_1127_;
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_inc(v_key_1136_);
lean_dec(v_v_1127_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
size_t v___x_1141_; size_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = lean_ptr_addr(v_x_1116_);
v___x_1142_ = lean_ptr_addr(v_key_1136_);
v___x_1143_ = lean_usize_dec_eq(v___x_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_del_object(v___x_1139_);
v___x_1144_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1136_, v_val_1137_, v_x_1116_, v_x_1117_);
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
v___y_1131_ = v___x_1145_;
goto v___jp_1130_;
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_val_1137_);
lean_dec(v_key_1136_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_x_1117_);
lean_ctor_set(v___x_1139_, 0, v_x_1116_);
v___x_1147_ = v___x_1139_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_x_1116_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_x_1117_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v___y_1131_ = v___x_1147_;
goto v___jp_1130_;
}
}
}
}
case 1:
{
lean_object* v_node_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1162_; 
v_node_1150_ = lean_ctor_get(v_v_1127_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_v_1127_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1152_ = v_v_1127_;
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_node_1150_);
lean_dec(v_v_1127_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1154_ = ((size_t)5ULL);
v___x_1155_ = lean_usize_shift_right(v_x_1114_, v___x_1154_);
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_x_1115_, v___x_1156_);
v___x_1158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_1150_, v___x_1155_, v___x_1157_, v_x_1116_, v_x_1117_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1158_);
v___x_1160_ = v___x_1152_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v___y_1131_ = v___x_1160_;
goto v___jp_1130_;
}
}
}
default: 
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_x_1116_);
lean_ctor_set(v___x_1163_, 1, v_x_1117_);
v___y_1131_ = v___x_1163_;
goto v___jp_1130_;
}
}
v___jp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_array_fset(v_xs_x27_1129_, v_j_1121_, v___y_1131_);
lean_dec(v_j_1121_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1132_);
v___x_1134_ = v___x_1125_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
else
{
lean_object* v_ks_1166_; lean_object* v_vs_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1187_; 
v_ks_1166_ = lean_ctor_get(v_x_1113_, 0);
v_vs_1167_ = lean_ctor_get(v_x_1113_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1169_ = v_x_1113_;
v_isShared_1170_ = v_isSharedCheck_1187_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_vs_1167_);
lean_inc(v_ks_1166_);
lean_dec(v_x_1113_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1187_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_ks_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_vs_1167_);
v___x_1172_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v_newNode_1173_; uint8_t v___y_1175_; size_t v___x_1181_; uint8_t v___x_1182_; 
v_newNode_1173_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_1172_, v_x_1116_, v_x_1117_);
v___x_1181_ = ((size_t)7ULL);
v___x_1182_ = lean_usize_dec_le(v___x_1181_, v_x_1115_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1173_);
v___x_1184_ = lean_unsigned_to_nat(4u);
v___x_1185_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
v___y_1175_ = v___x_1185_;
goto v___jp_1174_;
}
else
{
v___y_1175_ = v___x_1182_;
goto v___jp_1174_;
}
v___jp_1174_:
{
if (v___y_1175_ == 0)
{
lean_object* v_ks_1176_; lean_object* v_vs_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_ks_1176_ = lean_ctor_get(v_newNode_1173_, 0);
lean_inc_ref(v_ks_1176_);
v_vs_1177_ = lean_ctor_get(v_newNode_1173_, 1);
lean_inc_ref(v_vs_1177_);
lean_dec_ref(v_newNode_1173_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
v___x_1180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_1115_, v_ks_1176_, v_vs_1177_, v___x_1178_, v___x_1179_);
lean_dec_ref(v_vs_1177_);
lean_dec_ref(v_ks_1176_);
return v___x_1180_;
}
else
{
return v_newNode_1173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1188_, lean_object* v_keys_1189_, lean_object* v_vals_1190_, lean_object* v_i_1191_, lean_object* v_entries_1192_){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_array_get_size(v_keys_1189_);
v___x_1194_ = lean_nat_dec_lt(v_i_1191_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec(v_i_1191_);
return v_entries_1192_;
}
else
{
lean_object* v_k_1195_; lean_object* v_v_1196_; size_t v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; uint64_t v___x_1200_; size_t v_h_1201_; size_t v___x_1202_; lean_object* v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v_h_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_k_1195_ = lean_array_fget_borrowed(v_keys_1189_, v_i_1191_);
v_v_1196_ = lean_array_fget_borrowed(v_vals_1190_, v_i_1191_);
v___x_1197_ = lean_ptr_addr(v_k_1195_);
v___x_1198_ = ((size_t)3ULL);
v___x_1199_ = lean_usize_shift_right(v___x_1197_, v___x_1198_);
v___x_1200_ = lean_usize_to_uint64(v___x_1199_);
v_h_1201_ = lean_uint64_to_usize(v___x_1200_);
v___x_1202_ = ((size_t)5ULL);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_sub(v_depth_1188_, v___x_1204_);
v___x_1206_ = lean_usize_mul(v___x_1202_, v___x_1205_);
v_h_1207_ = lean_usize_shift_right(v_h_1201_, v___x_1206_);
v___x_1208_ = lean_nat_add(v_i_1191_, v___x_1203_);
lean_dec(v_i_1191_);
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
v___x_1209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_1192_, v_h_1207_, v_depth_1188_, v_k_1195_, v_v_1196_);
v_i_1191_ = v___x_1208_;
v_entries_1192_ = v___x_1209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1211_, lean_object* v_keys_1212_, lean_object* v_vals_1213_, lean_object* v_i_1214_, lean_object* v_entries_1215_){
_start:
{
size_t v_depth_boxed_1216_; lean_object* v_res_1217_; 
v_depth_boxed_1216_ = lean_unbox_usize(v_depth_1211_);
lean_dec(v_depth_1211_);
v_res_1217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1216_, v_keys_1212_, v_vals_1213_, v_i_1214_, v_entries_1215_);
lean_dec_ref(v_vals_1213_);
lean_dec_ref(v_keys_1212_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(lean_object* v_x_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
size_t v_x_423__boxed_1223_; size_t v_x_424__boxed_1224_; lean_object* v_res_1225_; 
v_x_423__boxed_1223_ = lean_unbox_usize(v_x_1219_);
lean_dec(v_x_1219_);
v_x_424__boxed_1224_ = lean_unbox_usize(v_x_1220_);
lean_dec(v_x_1220_);
v_res_1225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1218_, v_x_423__boxed_1223_, v_x_424__boxed_1224_, v_x_1221_, v_x_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_){
_start:
{
size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; uint64_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1229_ = lean_ptr_addr(v_x_1227_);
v___x_1230_ = ((size_t)3ULL);
v___x_1231_ = lean_usize_shift_right(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_usize_to_uint64(v___x_1231_);
v___x_1233_ = lean_uint64_to_usize(v___x_1232_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1226_, v___x_1233_, v___x_1234_, v_x_1227_, v_x_1228_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(lean_object* v_m_1236_, lean_object* v_e_1237_, lean_object* v_opId_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_m_1236_, v_e_1237_);
if (lean_obj_tag(v___x_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_1238_, v_val_1240_);
v___x_1242_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1236_, v_e_1237_, v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v___x_1239_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_opId_1238_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_1236_, v_e_1237_, v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_1247_, v_x_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, size_t v_x_1253_, size_t v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_1252_, v_x_1253_, v_x_1254_, v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_628__boxed_1264_; size_t v_x_629__boxed_1265_; lean_object* v_res_1266_; 
v_x_628__boxed_1264_ = lean_unbox_usize(v_x_1260_);
lean_dec(v_x_1260_);
v_x_629__boxed_1265_ = lean_unbox_usize(v_x_1261_);
lean_dec(v_x_1261_);
v_res_1266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_1258_, v_x_1259_, v_x_628__boxed_1264_, v_x_629__boxed_1265_, v_x_1262_, v_x_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1267_, lean_object* v_n_1268_, lean_object* v_k_1269_, lean_object* v_v_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_1268_, v_k_1269_, v_v_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1272_, size_t v_depth_1273_, lean_object* v_keys_1274_, lean_object* v_vals_1275_, lean_object* v_heq_1276_, lean_object* v_i_1277_, lean_object* v_entries_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_1273_, v_keys_1274_, v_vals_1275_, v_i_1277_, v_entries_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_depth_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_heq_1284_, lean_object* v_i_1285_, lean_object* v_entries_1286_){
_start:
{
size_t v_depth_boxed_1287_; lean_object* v_res_1288_; 
v_depth_boxed_1287_ = lean_unbox_usize(v_depth_1281_);
lean_dec(v_depth_1281_);
v_res_1288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_1280_, v_depth_boxed_1287_, v_keys_1282_, v_vals_1283_, v_heq_1284_, v_i_1285_, v_entries_1286_);
lean_dec_ref(v_vals_1283_);
lean_dec_ref(v_keys_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1290_, v_x_1291_, v_x_1292_, v_x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(lean_object* v_e_1295_, lean_object* v_a_1296_, lean_object* v_s_1297_){
_start:
{
lean_object* v_structs_1298_; lean_object* v_opIdOf_1299_; lean_object* v_exprToOpIds_1300_; lean_object* v_steps_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_structs_1298_ = lean_ctor_get(v_s_1297_, 0);
v_opIdOf_1299_ = lean_ctor_get(v_s_1297_, 1);
v_exprToOpIds_1300_ = lean_ctor_get(v_s_1297_, 2);
v_steps_1301_ = lean_ctor_get(v_s_1297_, 3);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_s_1297_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1303_ = v_s_1297_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_steps_1301_);
lean_inc(v_exprToOpIds_1300_);
lean_inc(v_opIdOf_1299_);
lean_inc(v_structs_1298_);
lean_dec(v_s_1297_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_inc(v_a_1296_);
v___x_1305_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(v_exprToOpIds_1300_, v_e_1295_, v_a_1296_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 2, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_structs_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_opIdOf_1299_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_steps_1301_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(lean_object* v_e_1310_, lean_object* v_a_1311_, lean_object* v_s_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_1310_, v_a_1311_, v_s_1312_);
lean_dec(v_a_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg(lean_object* v_e_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_inc(v_a_1315_);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1318_, 0, v_e_1314_);
lean_closure_set(v___f_1318_, 1, v_a_1315_);
v___x_1319_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1320_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1319_, v___f_1318_, v_a_1316_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(lean_object* v_e_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec(v_a_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId(lean_object* v_e_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1326_, v_a_1327_, v_a_1328_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_addTermOpId___boxed(lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Meta_Grind_AC_addTermOpId(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec(v_a_1341_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___lam__0(lean_object* v_e_1354_, lean_object* v_size_1355_, lean_object* v_s_1356_){
_start:
{
lean_object* v_id_1357_; lean_object* v_type_1358_; lean_object* v_u_1359_; lean_object* v_op_1360_; lean_object* v_neutral_x3f_1361_; lean_object* v_assocInst_1362_; lean_object* v_idempotentInst_x3f_1363_; lean_object* v_commInst_x3f_1364_; lean_object* v_neutralInst_x3f_1365_; lean_object* v_nextId_1366_; lean_object* v_vars_1367_; lean_object* v_varMap_1368_; lean_object* v_denote_1369_; lean_object* v_denoteEntries_1370_; lean_object* v_queue_1371_; lean_object* v_basis_1372_; lean_object* v_diseqs_1373_; uint8_t v_recheck_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1383_; 
v_id_1357_ = lean_ctor_get(v_s_1356_, 0);
v_type_1358_ = lean_ctor_get(v_s_1356_, 1);
v_u_1359_ = lean_ctor_get(v_s_1356_, 2);
v_op_1360_ = lean_ctor_get(v_s_1356_, 3);
v_neutral_x3f_1361_ = lean_ctor_get(v_s_1356_, 4);
v_assocInst_1362_ = lean_ctor_get(v_s_1356_, 5);
v_idempotentInst_x3f_1363_ = lean_ctor_get(v_s_1356_, 6);
v_commInst_x3f_1364_ = lean_ctor_get(v_s_1356_, 7);
v_neutralInst_x3f_1365_ = lean_ctor_get(v_s_1356_, 8);
v_nextId_1366_ = lean_ctor_get(v_s_1356_, 9);
v_vars_1367_ = lean_ctor_get(v_s_1356_, 10);
v_varMap_1368_ = lean_ctor_get(v_s_1356_, 11);
v_denote_1369_ = lean_ctor_get(v_s_1356_, 12);
v_denoteEntries_1370_ = lean_ctor_get(v_s_1356_, 13);
v_queue_1371_ = lean_ctor_get(v_s_1356_, 14);
v_basis_1372_ = lean_ctor_get(v_s_1356_, 15);
v_diseqs_1373_ = lean_ctor_get(v_s_1356_, 16);
v_recheck_1374_ = lean_ctor_get_uint8(v_s_1356_, sizeof(void*)*17);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_s_1356_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1376_ = v_s_1356_;
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_diseqs_1373_);
lean_inc(v_basis_1372_);
lean_inc(v_queue_1371_);
lean_inc(v_denoteEntries_1370_);
lean_inc(v_denote_1369_);
lean_inc(v_varMap_1368_);
lean_inc(v_vars_1367_);
lean_inc(v_nextId_1366_);
lean_inc(v_neutralInst_x3f_1365_);
lean_inc(v_commInst_x3f_1364_);
lean_inc(v_idempotentInst_x3f_1363_);
lean_inc(v_assocInst_1362_);
lean_inc(v_neutral_x3f_1361_);
lean_inc(v_op_1360_);
lean_inc(v_u_1359_);
lean_inc(v_type_1358_);
lean_inc(v_id_1357_);
lean_dec(v_s_1356_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_inc_ref(v_e_1354_);
v___x_1378_ = l_Lean_PersistentArray_push___redArg(v_vars_1367_, v_e_1354_);
v___x_1379_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_1368_, v_e_1354_, v_size_1355_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 11, v___x_1379_);
lean_ctor_set(v___x_1376_, 10, v___x_1378_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_id_1357_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_type_1358_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v_u_1359_);
lean_ctor_set(v_reuseFailAlloc_1382_, 3, v_op_1360_);
lean_ctor_set(v_reuseFailAlloc_1382_, 4, v_neutral_x3f_1361_);
lean_ctor_set(v_reuseFailAlloc_1382_, 5, v_assocInst_1362_);
lean_ctor_set(v_reuseFailAlloc_1382_, 6, v_idempotentInst_x3f_1363_);
lean_ctor_set(v_reuseFailAlloc_1382_, 7, v_commInst_x3f_1364_);
lean_ctor_set(v_reuseFailAlloc_1382_, 8, v_neutralInst_x3f_1365_);
lean_ctor_set(v_reuseFailAlloc_1382_, 9, v_nextId_1366_);
lean_ctor_set(v_reuseFailAlloc_1382_, 10, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1382_, 11, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 12, v_denote_1369_);
lean_ctor_set(v_reuseFailAlloc_1382_, 13, v_denoteEntries_1370_);
lean_ctor_set(v_reuseFailAlloc_1382_, 14, v_queue_1371_);
lean_ctor_set(v_reuseFailAlloc_1382_, 15, v_basis_1372_);
lean_ctor_set(v_reuseFailAlloc_1382_, 16, v_diseqs_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1382_, sizeof(void*)*17, v_recheck_1374_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar(lean_object* v_e_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1447_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1447_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1447_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_vars_1402_; lean_object* v_varMap_1403_; lean_object* v___x_1404_; 
v_vars_1402_ = lean_ctor_get(v_a_1398_, 10);
lean_inc_ref(v_vars_1402_);
v_varMap_1403_ = lean_ctor_get(v_a_1398_, 11);
lean_inc_ref(v_varMap_1403_);
lean_dec(v_a_1398_);
v___x_1404_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_1403_, v_e_1384_);
lean_dec_ref(v_varMap_1403_);
if (lean_obj_tag(v___x_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1407_; 
lean_dec_ref(v_vars_1402_);
lean_dec_ref(v_e_1384_);
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v___x_1404_, 1);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v_val_1405_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_val_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v_size_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; 
lean_dec(v___x_1404_);
lean_del_object(v___x_1400_);
v_size_1409_ = lean_ctor_get(v_vars_1402_, 2);
lean_inc_n(v_size_1409_, 2);
lean_dec_ref(v_vars_1402_);
lean_inc_ref(v_e_1384_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_mkVar___lam__0), 3, 2);
lean_closure_set(v___f_1410_, 0, v_e_1384_);
lean_closure_set(v___f_1410_, 1, v_size_1409_);
v___x_1411_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v___f_1410_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v___x_1412_; 
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_e_1384_);
v___x_1412_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_dec_ref_known(v___x_1412_, 1);
v___x_1413_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1414_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1413_, v_e_1384_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1422_);
v___x_1416_ = v___x_1414_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v___x_1414_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_size_1409_);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_size_1409_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_size_1409_);
v_a_1423_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1414_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1414_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_size_1409_);
lean_dec_ref(v_e_1384_);
v_a_1431_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1412_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1412_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_size_1409_);
lean_dec_ref(v_e_1384_);
v_a_1439_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1411_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1411_);
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
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_e_1384_);
v_a_1448_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1397_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1397_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_mkVar___boxed(lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_Grind_AC_mkVar(v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec(v_a_1457_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(lean_object* v_e_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_mctx_1474_; lean_object* v___x_1475_; lean_object* v_fst_1476_; lean_object* v_snd_1477_; lean_object* v___x_1478_; lean_object* v_cache_1479_; lean_object* v_zetaDeltaFVarIds_1480_; lean_object* v_postponed_1481_; lean_object* v_diag_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1491_; 
v___x_1473_ = lean_st_ref_get(v___y_1471_);
v_mctx_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_mctx_1474_);
lean_dec(v___x_1473_);
v___x_1475_ = lean_instantiate_expr_mvars(v_mctx_1474_, v_e_1470_);
v_fst_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_fst_1476_);
v_snd_1477_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_snd_1477_);
lean_dec_ref(v___x_1475_);
v___x_1478_ = lean_st_ref_take(v___y_1471_);
v_cache_1479_ = lean_ctor_get(v___x_1478_, 1);
v_zetaDeltaFVarIds_1480_ = lean_ctor_get(v___x_1478_, 2);
v_postponed_1481_ = lean_ctor_get(v___x_1478_, 3);
v_diag_1482_ = lean_ctor_get(v___x_1478_, 4);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1492_);
v___x_1484_ = v___x_1478_;
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_diag_1482_);
lean_inc(v_postponed_1481_);
lean_inc(v_zetaDeltaFVarIds_1480_);
lean_inc(v_cache_1479_);
lean_dec(v___x_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_fst_1476_);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_fst_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_cache_1479_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_zetaDeltaFVarIds_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_postponed_1481_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_diag_1482_);
v___x_1487_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_st_ref_set(v___y_1471_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_snd_1477_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(lean_object* v_e_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1493_, v___y_1494_);
lean_dec(v___y_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(lean_object* v_e_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_1497_, v___y_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(lean_object* v_e_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec(v___y_1511_);
return v_res_1522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(32u);
v___x_1524_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1(void){
_start:
{
size_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1526_ = ((size_t)5ULL);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_unsigned_to_nat(32u);
v___x_1529_ = lean_mk_empty_array_with_capacity(v___x_1528_);
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
v___x_1531_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1529_);
lean_ctor_set(v___x_1531_, 2, v___x_1527_);
lean_ctor_set(v___x_1531_, 3, v___x_1527_);
lean_ctor_set_usize(v___x_1531_, 4, v___x_1526_);
return v___x_1531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(lean_object* v___x_1535_, lean_object* v_binderType_1536_, lean_object* v_a_1537_, lean_object* v_op_1538_, lean_object* v_snd_1539_, lean_object* v_val_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_fst_1543_, uint8_t v_a_1544_, lean_object* v_s_1545_){
_start:
{
lean_object* v_structs_1546_; lean_object* v_opIdOf_1547_; lean_object* v_exprToOpIds_1548_; lean_object* v_steps_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1563_; 
v_structs_1546_ = lean_ctor_get(v_s_1545_, 0);
v_opIdOf_1547_ = lean_ctor_get(v_s_1545_, 1);
v_exprToOpIds_1548_ = lean_ctor_get(v_s_1545_, 2);
v_steps_1549_ = lean_ctor_get(v_s_1545_, 3);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_s_1545_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1551_ = v_s_1545_;
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_steps_1549_);
lean_inc(v_exprToOpIds_1548_);
lean_inc(v_opIdOf_1547_);
lean_inc(v_structs_1546_);
lean_dec(v_s_1545_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1563_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
v___x_1555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
v___x_1556_ = lean_box(1);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_1558_, 0, v___x_1535_);
lean_ctor_set(v___x_1558_, 1, v_binderType_1536_);
lean_ctor_set(v___x_1558_, 2, v_a_1537_);
lean_ctor_set(v___x_1558_, 3, v_op_1538_);
lean_ctor_set(v___x_1558_, 4, v_snd_1539_);
lean_ctor_set(v___x_1558_, 5, v_val_1540_);
lean_ctor_set(v___x_1558_, 6, v_a_1541_);
lean_ctor_set(v___x_1558_, 7, v_a_1542_);
lean_ctor_set(v___x_1558_, 8, v_fst_1543_);
lean_ctor_set(v___x_1558_, 9, v___x_1553_);
lean_ctor_set(v___x_1558_, 10, v___x_1554_);
lean_ctor_set(v___x_1558_, 11, v___x_1555_);
lean_ctor_set(v___x_1558_, 12, v___x_1555_);
lean_ctor_set(v___x_1558_, 13, v___x_1554_);
lean_ctor_set(v___x_1558_, 14, v___x_1556_);
lean_ctor_set(v___x_1558_, 15, v___x_1557_);
lean_ctor_set(v___x_1558_, 16, v___x_1554_);
lean_ctor_set_uint8(v___x_1558_, sizeof(void*)*17, v_a_1544_);
v___x_1559_ = lean_array_push(v_structs_1546_, v___x_1558_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1559_);
v___x_1561_ = v___x_1551_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_opIdOf_1547_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_exprToOpIds_1548_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_steps_1549_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(lean_object* v___x_1564_, lean_object* v_binderType_1565_, lean_object* v_a_1566_, lean_object* v_op_1567_, lean_object* v_snd_1568_, lean_object* v_val_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_fst_1572_, lean_object* v_a_1573_, lean_object* v_s_1574_){
_start:
{
uint8_t v_a_174801__boxed_1575_; lean_object* v_res_1576_; 
v_a_174801__boxed_1575_ = lean_unbox(v_a_1573_);
v_res_1576_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(v___x_1564_, v_binderType_1565_, v_a_1566_, v_op_1567_, v_snd_1568_, v_val_1569_, v_a_1570_, v_a_1571_, v_fst_1572_, v_a_174801__boxed_1575_, v_s_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(lean_object* v_m_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_buckets_1579_; lean_object* v___x_1580_; uint64_t v___y_1582_; 
v_buckets_1579_ = lean_ctor_get(v_m_1577_, 1);
v___x_1580_ = lean_array_get_size(v_buckets_1579_);
if (lean_obj_tag(v_a_1578_) == 0)
{
uint64_t v___x_1596_; 
v___x_1596_ = 1723ULL;
v___y_1582_ = v___x_1596_;
goto v___jp_1581_;
}
else
{
uint64_t v_hash_1597_; 
v_hash_1597_ = lean_ctor_get_uint64(v_a_1578_, sizeof(void*)*2);
v___y_1582_ = v_hash_1597_;
goto v___jp_1581_;
}
v___jp_1581_:
{
uint64_t v___x_1583_; uint64_t v___x_1584_; uint64_t v_fold_1585_; uint64_t v___x_1586_; uint64_t v___x_1587_; uint64_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1583_ = 32ULL;
v___x_1584_ = lean_uint64_shift_right(v___y_1582_, v___x_1583_);
v_fold_1585_ = lean_uint64_xor(v___y_1582_, v___x_1584_);
v___x_1586_ = 16ULL;
v___x_1587_ = lean_uint64_shift_right(v_fold_1585_, v___x_1586_);
v___x_1588_ = lean_uint64_xor(v_fold_1585_, v___x_1587_);
v___x_1589_ = lean_uint64_to_usize(v___x_1588_);
v___x_1590_ = lean_usize_of_nat(v___x_1580_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_sub(v___x_1590_, v___x_1591_);
v___x_1593_ = lean_usize_land(v___x_1589_, v___x_1592_);
v___x_1594_ = lean_array_uget_borrowed(v_buckets_1579_, v___x_1593_);
v___x_1595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_1578_, v___x_1594_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(lean_object* v_m_1598_, lean_object* v_a_1599_){
_start:
{
uint8_t v_res_1600_; lean_object* v_r_1601_; 
v_res_1600_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_m_1598_);
v_r_1601_ = lean_box(v_res_1600_);
return v_r_1601_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1602_; double v___x_1603_; 
v___x_1602_ = lean_unsigned_to_nat(0u);
v___x_1603_ = lean_float_of_nat(v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(lean_object* v_cls_1607_, lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_ref_1614_; lean_object* v___x_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1660_; 
v_ref_1614_ = lean_ctor_get(v___y_1611_, 5);
v___x_1615_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1660_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1660_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v_traceState_1621_; lean_object* v_env_1622_; lean_object* v_nextMacroScope_1623_; lean_object* v_ngen_1624_; lean_object* v_auxDeclNGen_1625_; lean_object* v_cache_1626_; lean_object* v_messages_1627_; lean_object* v_infoState_1628_; lean_object* v_snapshotTasks_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1659_; 
v___x_1620_ = lean_st_ref_take(v___y_1612_);
v_traceState_1621_ = lean_ctor_get(v___x_1620_, 4);
v_env_1622_ = lean_ctor_get(v___x_1620_, 0);
v_nextMacroScope_1623_ = lean_ctor_get(v___x_1620_, 1);
v_ngen_1624_ = lean_ctor_get(v___x_1620_, 2);
v_auxDeclNGen_1625_ = lean_ctor_get(v___x_1620_, 3);
v_cache_1626_ = lean_ctor_get(v___x_1620_, 5);
v_messages_1627_ = lean_ctor_get(v___x_1620_, 6);
v_infoState_1628_ = lean_ctor_get(v___x_1620_, 7);
v_snapshotTasks_1629_ = lean_ctor_get(v___x_1620_, 8);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1631_ = v___x_1620_;
v_isShared_1632_ = v_isSharedCheck_1659_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_snapshotTasks_1629_);
lean_inc(v_infoState_1628_);
lean_inc(v_messages_1627_);
lean_inc(v_cache_1626_);
lean_inc(v_traceState_1621_);
lean_inc(v_auxDeclNGen_1625_);
lean_inc(v_ngen_1624_);
lean_inc(v_nextMacroScope_1623_);
lean_inc(v_env_1622_);
lean_dec(v___x_1620_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1659_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
uint64_t v_tid_1633_; lean_object* v_traces_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1658_; 
v_tid_1633_ = lean_ctor_get_uint64(v_traceState_1621_, sizeof(void*)*1);
v_traces_1634_ = lean_ctor_get(v_traceState_1621_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_traceState_1621_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1636_ = v_traceState_1621_;
v_isShared_1637_ = v_isSharedCheck_1658_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_traces_1634_);
lean_dec(v_traceState_1621_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1658_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; double v___x_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
v___x_1640_ = 0;
v___x_1641_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1));
v___x_1642_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1642_, 0, v_cls_1607_);
lean_ctor_set(v___x_1642_, 1, v___x_1638_);
lean_ctor_set(v___x_1642_, 2, v___x_1641_);
lean_ctor_set_float(v___x_1642_, sizeof(void*)*3, v___x_1639_);
lean_ctor_set_float(v___x_1642_, sizeof(void*)*3 + 8, v___x_1639_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*3 + 16, v___x_1640_);
v___x_1643_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2));
v___x_1644_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v_a_1616_);
lean_ctor_set(v___x_1644_, 2, v___x_1643_);
lean_inc(v_ref_1614_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v_ref_1614_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_PersistentArray_push___redArg(v_traces_1634_, v___x_1645_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1646_);
v___x_1648_ = v___x_1636_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1646_);
lean_ctor_set_uint64(v_reuseFailAlloc_1657_, sizeof(void*)*1, v_tid_1633_);
v___x_1648_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1650_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v___x_1648_);
v___x_1650_ = v___x_1631_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_env_1622_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_nextMacroScope_1623_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_ngen_1624_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_auxDeclNGen_1625_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_cache_1626_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v_messages_1627_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_infoState_1628_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v_snapshotTasks_1629_);
v___x_1650_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1651_ = lean_st_ref_set(v___y_1612_, v___x_1650_);
v___x_1652_ = lean_box(0);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1652_);
v___x_1654_ = v___x_1618_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(lean_object* v_cls_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_1661_, v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3));
v___x_1676_ = l_Lean_MessageData_ofFormat(v___x_1675_);
return v___x_1676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5));
v___x_1679_ = l_Lean_stringToMessageData(v___x_1678_);
return v___x_1679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15));
v___x_1696_ = l_Lean_Name_append(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__29));
v___x_1722_ = l_Lean_mkConst(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(lean_object* v_op_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___y_1736_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; uint8_t v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v_neutral_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v_f_1944_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; 
v_f_1944_ = l_Lean_Expr_getAppFn(v_op_1723_);
if (lean_obj_tag(v_f_1944_) == 4)
{
lean_object* v_declName_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_declName_2197_ = lean_ctor_get(v_f_1944_, 0);
lean_inc(v_declName_2197_);
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
v___x_2199_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_2198_, v_declName_2197_);
lean_dec(v_declName_2197_);
if (v___x_2199_ == 0)
{
v___y_1946_ = v_a_1724_;
v___y_1947_ = v_a_1725_;
v___y_1948_ = v_a_1726_;
v___y_1949_ = v_a_1727_;
v___y_1950_ = v_a_1728_;
v___y_1951_ = v_a_1729_;
v___y_1952_ = v_a_1730_;
v___y_1953_ = v_a_1731_;
v___y_1954_ = v_a_1732_;
v___y_1955_ = v_a_1733_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec_ref_known(v_f_1944_, 2);
lean_dec_ref(v_op_1723_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
else
{
v___y_1946_ = v_a_1724_;
v___y_1947_ = v_a_1725_;
v___y_1948_ = v_a_1726_;
v___y_1949_ = v_a_1727_;
v___y_1950_ = v_a_1728_;
v___y_1951_ = v_a_1729_;
v___y_1952_ = v_a_1730_;
v___y_1953_ = v_a_1731_;
v___y_1954_ = v_a_1732_;
v___y_1955_ = v_a_1733_;
goto v___jp_1945_;
}
v___jp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
v___jp_1739_:
{
if (lean_obj_tag(v___y_1741_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1753_; 
v_val_1752_ = lean_ctor_get(v___y_1741_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v___y_1741_, 1);
v___x_1753_ = l_Lean_Meta_Grind_AC_mkVar(v_val_1752_, v___y_1740_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_dec_ref_known(v___x_1753_, 1);
v___y_1736_ = v___y_1740_;
goto v___jp_1735_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v___y_1740_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_dec(v___y_1741_);
v___y_1736_ = v___y_1740_;
goto v___jp_1735_;
}
}
v___jp_1762_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1769_);
lean_ctor_set(v___x_1778_, 1, v___y_1777_);
lean_inc(v___y_1765_);
v___x_1779_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_1765_, v___x_1778_, v___y_1774_, v___y_1770_, v___y_1764_, v___y_1775_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_dec_ref_known(v___x_1779_, 1);
v___y_1740_ = v___y_1767_;
v___y_1741_ = v___y_1766_;
v___y_1742_ = v___y_1776_;
v___y_1743_ = v___y_1772_;
v___y_1744_ = v___y_1773_;
v___y_1745_ = v___y_1768_;
v___y_1746_ = v___y_1763_;
v___y_1747_ = v___y_1771_;
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___y_1764_;
v___y_1751_ = v___y_1775_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
v___jp_1788_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_inc_ref(v___y_1803_);
v___x_1804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1803_);
v___x_1805_ = l_Lean_MessageData_ofFormat(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___y_1800_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
if (lean_obj_tag(v___y_1792_) == 0)
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1790_;
v___y_1765_ = v___y_1791_;
v___y_1766_ = v___y_1792_;
v___y_1767_ = v___y_1793_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___x_1808_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1797_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___y_1802_;
v___y_1777_ = v___x_1809_;
goto v___jp_1762_;
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1811_; 
v_val_1810_ = lean_ctor_get(v___y_1792_, 0);
lean_inc(v_val_1810_);
v___x_1811_ = l_Lean_MessageData_ofExpr(v_val_1810_);
v___y_1763_ = v___y_1789_;
v___y_1764_ = v___y_1790_;
v___y_1765_ = v___y_1791_;
v___y_1766_ = v___y_1792_;
v___y_1767_ = v___y_1793_;
v___y_1768_ = v___y_1794_;
v___y_1769_ = v___x_1808_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1796_;
v___y_1772_ = v___y_1797_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___y_1802_;
v___y_1777_ = v___x_1811_;
goto v___jp_1762_;
}
}
v___jp_1812_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_inc_ref(v___y_1828_);
v___x_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___y_1828_);
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___y_1813_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
if (lean_obj_tag(v___y_1820_) == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1789_ = v___y_1814_;
v___y_1790_ = v___y_1815_;
v___y_1791_ = v___y_1816_;
v___y_1792_ = v___y_1817_;
v___y_1793_ = v___y_1818_;
v___y_1794_ = v___y_1819_;
v___y_1795_ = v___y_1821_;
v___y_1796_ = v___y_1822_;
v___y_1797_ = v___y_1823_;
v___y_1798_ = v___y_1824_;
v___y_1799_ = v___y_1825_;
v___y_1800_ = v___x_1833_;
v___y_1801_ = v___y_1826_;
v___y_1802_ = v___y_1827_;
v___y_1803_ = v___x_1834_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1835_; 
lean_dec_ref_known(v___y_1820_, 1);
v___x_1835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1789_ = v___y_1814_;
v___y_1790_ = v___y_1815_;
v___y_1791_ = v___y_1816_;
v___y_1792_ = v___y_1817_;
v___y_1793_ = v___y_1818_;
v___y_1794_ = v___y_1819_;
v___y_1795_ = v___y_1821_;
v___y_1796_ = v___y_1822_;
v___y_1797_ = v___y_1823_;
v___y_1798_ = v___y_1824_;
v___y_1799_ = v___y_1825_;
v___y_1800_ = v___x_1833_;
v___y_1801_ = v___y_1826_;
v___y_1802_ = v___y_1827_;
v___y_1803_ = v___x_1835_;
goto v___jp_1788_;
}
}
v___jp_1836_:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_1847_, v___y_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_structs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v_structs_1859_ = lean_ctor_get(v_a_1858_, 0);
lean_inc_ref(v_structs_1859_);
lean_dec(v_a_1858_);
v___x_1860_ = lean_array_get_size(v_structs_1859_);
lean_dec_ref(v_structs_1859_);
v___x_1861_ = lean_box(v___y_1840_);
lean_inc(v_snd_1846_);
lean_inc_ref(v_op_1723_);
v___f_1862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed), 11, 10);
lean_closure_set(v___f_1862_, 0, v___x_1860_);
lean_closure_set(v___f_1862_, 1, v___y_1838_);
lean_closure_set(v___f_1862_, 2, v___y_1837_);
lean_closure_set(v___f_1862_, 3, v_op_1723_);
lean_closure_set(v___f_1862_, 4, v_snd_1846_);
lean_closure_set(v___f_1862_, 5, v___y_1841_);
lean_closure_set(v___f_1862_, 6, v___y_1842_);
lean_closure_set(v___f_1862_, 7, v___y_1839_);
lean_closure_set(v___f_1862_, 8, v_fst_1845_);
lean_closure_set(v___f_1862_, 9, v___x_1861_);
v___x_1863_ = l_Lean_Meta_Grind_AC_acExt;
v___x_1864_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1863_, v___f_1862_, v___y_1847_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_options_1865_; uint8_t v_hasTrace_1866_; 
lean_dec_ref_known(v___x_1864_, 1);
v_options_1865_ = lean_ctor_get(v___y_1855_, 2);
v_hasTrace_1866_ = lean_ctor_get_uint8(v_options_1865_, sizeof(void*)*1);
if (v_hasTrace_1866_ == 0)
{
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v_op_1723_);
v___y_1740_ = v___x_1860_;
v___y_1741_ = v_snd_1846_;
v___y_1742_ = v___y_1847_;
v___y_1743_ = v___y_1848_;
v___y_1744_ = v___y_1849_;
v___y_1745_ = v___y_1850_;
v___y_1746_ = v___y_1851_;
v___y_1747_ = v___y_1852_;
v___y_1748_ = v___y_1853_;
v___y_1749_ = v___y_1854_;
v___y_1750_ = v___y_1855_;
v___y_1751_ = v___y_1856_;
goto v___jp_1739_;
}
else
{
lean_object* v_inheritedTraceOptions_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_inheritedTraceOptions_1867_ = lean_ctor_get(v___y_1855_, 13);
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13));
v___x_1869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
v___x_1870_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1867_, v_options_1865_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v_op_1723_);
v___y_1740_ = v___x_1860_;
v___y_1741_ = v_snd_1846_;
v___y_1742_ = v___y_1847_;
v___y_1743_ = v___y_1848_;
v___y_1744_ = v___y_1849_;
v___y_1745_ = v___y_1850_;
v___y_1746_ = v___y_1851_;
v___y_1747_ = v___y_1852_;
v___y_1748_ = v___y_1853_;
v___y_1749_ = v___y_1854_;
v___y_1750_ = v___y_1855_;
v___y_1751_ = v___y_1856_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = l_Lean_MessageData_ofExpr(v_op_1723_);
v___x_1872_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
if (lean_obj_tag(v___y_1843_) == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7));
v___y_1813_ = v___x_1873_;
v___y_1814_ = v___y_1851_;
v___y_1815_ = v___y_1855_;
v___y_1816_ = v___x_1868_;
v___y_1817_ = v_snd_1846_;
v___y_1818_ = v___x_1860_;
v___y_1819_ = v___y_1850_;
v___y_1820_ = v___y_1844_;
v___y_1821_ = v___y_1854_;
v___y_1822_ = v___y_1852_;
v___y_1823_ = v___y_1848_;
v___y_1824_ = v___y_1849_;
v___y_1825_ = v___y_1853_;
v___y_1826_ = v___y_1856_;
v___y_1827_ = v___y_1847_;
v___y_1828_ = v___x_1874_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1875_; 
lean_dec_ref_known(v___y_1843_, 1);
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8));
v___y_1813_ = v___x_1873_;
v___y_1814_ = v___y_1851_;
v___y_1815_ = v___y_1855_;
v___y_1816_ = v___x_1868_;
v___y_1817_ = v_snd_1846_;
v___y_1818_ = v___x_1860_;
v___y_1819_ = v___y_1850_;
v___y_1820_ = v___y_1844_;
v___y_1821_ = v___y_1854_;
v___y_1822_ = v___y_1852_;
v___y_1823_ = v___y_1848_;
v___y_1824_ = v___y_1849_;
v___y_1825_ = v___y_1853_;
v___y_1826_ = v___y_1856_;
v___y_1827_ = v___y_1847_;
v___y_1828_ = v___x_1875_;
goto v___jp_1812_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_snd_1846_);
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v_op_1723_);
v_a_1876_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1864_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1864_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_snd_1846_);
lean_dec(v_fst_1845_);
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v_op_1723_);
v_a_1884_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1857_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1857_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
v___jp_1892_:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_neutral_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_1723_, v___y_1903_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_box(0);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc(v_a_1914_);
v___x_1918_ = lean_grind_internalize(v_a_1914_, v_a_1916_, v___x_1917_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref_known(v___x_1918_, 1);
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1914_);
v___y_1837_ = v___y_1893_;
v___y_1838_ = v___y_1894_;
v___y_1839_ = v___y_1895_;
v___y_1840_ = v___y_1897_;
v___y_1841_ = v___y_1896_;
v___y_1842_ = v___y_1898_;
v___y_1843_ = v___y_1900_;
v___y_1844_ = v___y_1901_;
v_fst_1845_ = v___y_1899_;
v_snd_1846_ = v___x_1919_;
v___y_1847_ = v___y_1903_;
v___y_1848_ = v___y_1904_;
v___y_1849_ = v___y_1905_;
v___y_1850_ = v___y_1906_;
v___y_1851_ = v___y_1907_;
v___y_1852_ = v___y_1908_;
v___y_1853_ = v___y_1909_;
v___y_1854_ = v___y_1910_;
v___y_1855_ = v___y_1911_;
v___y_1856_ = v___y_1912_;
goto v___jp_1836_;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1914_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v_op_1723_);
v_a_1920_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1918_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1914_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v_op_1723_);
v_a_1928_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1915_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1915_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v_op_1723_);
v_a_1936_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1913_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1913_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
v___jp_1945_:
{
lean_object* v___x_1956_; 
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc_ref(v_op_1723_);
v___x_1956_ = lean_infer_type(v_op_1723_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
v___x_1958_ = lean_whnf(v_a_1957_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2180_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2180_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2180_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
if (lean_obj_tag(v_a_1959_) == 7)
{
lean_object* v_binderType_1963_; lean_object* v_body_1964_; uint8_t v___x_1965_; 
v_binderType_1963_ = lean_ctor_get(v_a_1959_, 1);
lean_inc_ref(v_binderType_1963_);
v_body_1964_ = lean_ctor_get(v_a_1959_, 2);
lean_inc_ref(v_body_1964_);
lean_dec_ref_known(v_a_1959_, 3);
v___x_1965_ = l_Lean_Expr_hasLooseBVars(v_body_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1961_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
v___x_1966_ = lean_whnf(v_body_1964_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2163_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_2163_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2163_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
if (lean_obj_tag(v_a_1967_) == 7)
{
lean_object* v_binderType_1971_; lean_object* v_body_1972_; uint8_t v___x_1973_; 
v_binderType_1971_ = lean_ctor_get(v_a_1967_, 1);
lean_inc_ref(v_binderType_1971_);
v_body_1972_ = lean_ctor_get(v_a_1967_, 2);
lean_inc_ref(v_body_1972_);
lean_dec_ref_known(v_a_1967_, 3);
v___x_1973_ = l_Lean_Expr_hasLooseBVars(v_body_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_del_object(v___x_1969_);
lean_inc_ref(v_binderType_1963_);
v___x_1974_ = l_Lean_Meta_isExprDefEq(v_binderType_1963_, v_binderType_1971_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2146_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2146_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2146_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_dec_ref(v_body_1972_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_1980_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1980_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_object* v___x_1984_; 
lean_del_object(v___x_1977_);
lean_inc_ref(v_binderType_1963_);
v___x_1984_ = l_Lean_Meta_isExprDefEq(v_binderType_1963_, v_body_1972_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2137_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_2137_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2137_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_1990_ = lean_box(0);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1990_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1994_; 
lean_del_object(v___x_1987_);
v___x_1994_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_1723_, v_f_1944_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec_ref(v_f_1944_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2128_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2128_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2128_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_unbox(v_a_1995_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_del_object(v___x_1997_);
lean_inc_ref(v_binderType_1963_);
v___x_2000_ = l_Lean_Meta_getLevel(v_binderType_1963_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc_n(v_a_2001_, 2);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21));
v___x_2003_ = lean_box(0);
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v_a_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
lean_inc_ref(v___x_2004_);
v___x_2005_ = l_Lean_mkConst(v___x_2002_, v___x_2004_);
lean_inc_ref(v_op_1723_);
lean_inc_ref(v_binderType_1963_);
v___x_2006_ = l_Lean_mkAppB(v___x_2005_, v_binderType_1963_, v_op_1723_);
v___x_2007_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2006_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2107_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2107_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2107_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_2010_);
v_val_2012_ = lean_ctor_get(v_a_2008_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_a_2008_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2014_ = v_a_2008_;
v_isShared_2015_ = v_isSharedCheck_2102_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_a_2008_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2102_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23));
lean_inc_ref(v___x_2004_);
v___x_2017_ = l_Lean_mkConst(v___x_2016_, v___x_2004_);
lean_inc_ref(v_op_1723_);
lean_inc_ref(v_binderType_1963_);
v___x_2018_ = l_Lean_mkAppB(v___x_2017_, v_binderType_1963_, v_op_1723_);
v___x_2019_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2018_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25));
lean_inc_ref(v___x_2004_);
v___x_2022_ = l_Lean_mkConst(v___x_2021_, v___x_2004_);
lean_inc_ref(v_op_1723_);
lean_inc_ref(v_binderType_1963_);
v___x_2023_ = l_Lean_mkAppB(v___x_2022_, v_binderType_1963_, v_op_1723_);
v___x_2024_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2023_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
lean_inc_ref(v_binderType_1963_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_binderType_1963_);
v___x_2027_ = v___x_2014_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_binderType_1963_);
v___x_2027_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = 0;
v___x_2029_ = lean_box(0);
v___x_2030_ = l_Lean_Meta_mkFreshExprMVar(v___x_2027_, v___x_2028_, v___x_2029_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_n(v_a_2031_, 2);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27));
v___x_2033_ = l_Lean_mkConst(v___x_2032_, v___x_2004_);
lean_inc_ref(v_op_1723_);
lean_inc_ref(v_binderType_1963_);
v___x_2034_ = l_Lean_mkApp3(v___x_2033_, v_binderType_1963_, v_op_1723_, v_a_2031_);
v___x_2035_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2034_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
if (lean_obj_tag(v_a_2036_) == 1)
{
lean_object* v___x_2037_; lean_object* v_a_2038_; lean_object* v___x_2039_; 
v___x_2037_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_2031_, v___y_1953_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_n(v_a_2038_, 2);
lean_dec_ref(v___x_2037_);
v___x_2039_ = l_Lean_Meta_getBitVecValue_x3f(v_a_2038_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_a_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_a_2038_);
v_val_2041_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v_a_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_val_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_val_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_val_2041_);
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30, &l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30_once, _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__30);
v___x_2045_ = l_Lean_mkNatLit(v_fst_2042_);
v___x_2046_ = l_Lean_Expr_app___override(v___x_2044_, v___x_2045_);
v___x_2047_ = l_Lean_Meta_mkNumeral(v___x_2046_, v_snd_2043_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; uint8_t v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
lean_inc(v_a_2025_);
lean_inc(v_a_2020_);
v___y_1893_ = v_a_2001_;
v___y_1894_ = v_binderType_1963_;
v___y_1895_ = v_a_2020_;
v___y_1896_ = v_val_2012_;
v___y_1897_ = v___x_2049_;
v___y_1898_ = v_a_2025_;
v___y_1899_ = v_a_2036_;
v___y_1900_ = v_a_2020_;
v___y_1901_ = v_a_2025_;
v_neutral_1902_ = v_a_2048_;
v___y_1903_ = v___y_1946_;
v___y_1904_ = v___y_1947_;
v___y_1905_ = v___y_1948_;
v___y_1906_ = v___y_1949_;
v___y_1907_ = v___y_1950_;
v___y_1908_ = v___y_1951_;
v___y_1909_ = v___y_1952_;
v___y_1910_ = v___y_1953_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1955_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref_known(v_a_2036_, 1);
lean_dec(v_a_2025_);
lean_dec(v_a_2020_);
lean_dec(v_val_2012_);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2050_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2047_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2047_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
uint8_t v___x_2058_; 
lean_dec(v_a_2040_);
v___x_2058_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
lean_inc(v_a_2025_);
lean_inc(v_a_2020_);
v___y_1893_ = v_a_2001_;
v___y_1894_ = v_binderType_1963_;
v___y_1895_ = v_a_2020_;
v___y_1896_ = v_val_2012_;
v___y_1897_ = v___x_2058_;
v___y_1898_ = v_a_2025_;
v___y_1899_ = v_a_2036_;
v___y_1900_ = v_a_2020_;
v___y_1901_ = v_a_2025_;
v_neutral_1902_ = v_a_2038_;
v___y_1903_ = v___y_1946_;
v___y_1904_ = v___y_1947_;
v___y_1905_ = v___y_1948_;
v___y_1906_ = v___y_1949_;
v___y_1907_ = v___y_1950_;
v___y_1908_ = v___y_1951_;
v___y_1909_ = v___y_1952_;
v___y_1910_ = v___y_1953_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1955_;
goto v___jp_1892_;
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2038_);
lean_dec_ref_known(v_a_2036_, 1);
lean_dec(v_a_2025_);
lean_dec(v_a_2020_);
lean_dec(v_val_2012_);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2059_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2039_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2039_);
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
lean_object* v___x_2067_; uint8_t v___x_2068_; 
lean_dec(v_a_2036_);
lean_dec(v_a_2031_);
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
lean_inc(v_a_2025_);
lean_inc(v_a_2020_);
v___y_1837_ = v_a_2001_;
v___y_1838_ = v_binderType_1963_;
v___y_1839_ = v_a_2020_;
v___y_1840_ = v___x_2068_;
v___y_1841_ = v_val_2012_;
v___y_1842_ = v_a_2025_;
v___y_1843_ = v_a_2020_;
v___y_1844_ = v_a_2025_;
v_fst_1845_ = v___x_2067_;
v_snd_1846_ = v___x_2067_;
v___y_1847_ = v___y_1946_;
v___y_1848_ = v___y_1947_;
v___y_1849_ = v___y_1948_;
v___y_1850_ = v___y_1949_;
v___y_1851_ = v___y_1950_;
v___y_1852_ = v___y_1951_;
v___y_1853_ = v___y_1952_;
v___y_1854_ = v___y_1953_;
v___y_1855_ = v___y_1954_;
v___y_1856_ = v___y_1955_;
goto v___jp_1836_;
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2031_);
lean_dec(v_a_2025_);
lean_dec(v_a_2020_);
lean_dec(v_val_2012_);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2069_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2035_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2035_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_2025_);
lean_dec(v_a_2020_);
lean_dec(v_val_2012_);
lean_dec_ref_known(v___x_2004_, 2);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2077_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2030_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2030_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_2020_);
lean_del_object(v___x_2014_);
lean_dec(v_val_2012_);
lean_dec_ref_known(v___x_2004_, 2);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2086_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2024_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2024_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_2014_);
lean_dec(v_val_2012_);
lean_dec_ref_known(v___x_2004_, 2);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2094_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2019_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2019_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec(v_a_2008_);
lean_dec_ref_known(v___x_2004_, 2);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v___x_2103_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2103_);
v___x_2105_ = v___x_2010_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref_known(v___x_2004_, 2);
lean_dec(v_a_2001_);
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2108_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2007_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2007_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2116_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2000_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2000_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
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
lean_object* v___x_2124_; lean_object* v___x_2126_; 
lean_dec(v_a_1995_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v___x_2124_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2124_);
v___x_2126_ = v___x_1997_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
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
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_op_1723_);
v_a_2129_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_1994_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_1994_);
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
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v_a_2138_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_1984_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_1984_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_body_1972_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v_a_2147_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_1974_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_1974_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec_ref(v_body_1972_);
lean_dec_ref(v_binderType_1971_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_2155_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2155_);
v___x_2157_ = v___x_1969_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_1967_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_2159_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2159_);
v___x_2161_ = v___x_1969_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v_a_2164_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_1966_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_1966_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec_ref(v_body_1964_);
lean_dec_ref(v_binderType_1963_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_2172_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_2172_);
v___x_2174_ = v___x_1961_;
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
else
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec(v_a_1959_);
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v___x_2176_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_2176_);
v___x_2178_ = v___x_1961_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v_a_2181_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_1958_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_1958_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_f_1944_);
lean_dec_ref(v_op_1723_);
v_a_2189_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_1956_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_1956_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(lean_object* v_op_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec(v_a_2203_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(lean_object* v_cls_2215_, lean_object* v_msg_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_2215_, v_msg_2216_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(lean_object* v_cls_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_2229_, v_msg_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
return v_res_2242_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(lean_object* v_00_u03b2_2243_, lean_object* v_m_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v___x_2246_; 
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_2244_, v_a_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(lean_object* v_00_u03b2_2247_, lean_object* v_m_2248_, lean_object* v_a_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_2247_, v_m_2248_, v_a_2249_);
lean_dec(v_a_2249_);
lean_dec_ref(v_m_2248_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(lean_object* v_op_2252_, lean_object* v_a_2253_, lean_object* v_s_2254_){
_start:
{
lean_object* v_structs_2255_; lean_object* v_opIdOf_2256_; lean_object* v_exprToOpIds_2257_; lean_object* v_steps_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2266_; 
v_structs_2255_ = lean_ctor_get(v_s_2254_, 0);
v_opIdOf_2256_ = lean_ctor_get(v_s_2254_, 1);
v_exprToOpIds_2257_ = lean_ctor_get(v_s_2254_, 2);
v_steps_2258_ = lean_ctor_get(v_s_2254_, 3);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_s_2254_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2260_ = v_s_2254_;
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_steps_2258_);
lean_inc(v_exprToOpIds_2257_);
lean_inc(v_opIdOf_2256_);
lean_inc(v_structs_2255_);
lean_dec(v_s_2254_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2266_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_2256_, v_op_2252_, v_a_2253_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_structs_2255_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_exprToOpIds_2257_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_steps_2258_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f(lean_object* v_op_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2268_, v_a_2276_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2311_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2311_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2311_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_opIdOf_2284_; lean_object* v___x_2285_; 
v_opIdOf_2284_ = lean_ctor_get(v_a_2280_, 1);
lean_inc_ref(v_opIdOf_2284_);
lean_dec(v_a_2280_);
v___x_2285_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_2284_, v_op_2267_);
lean_dec_ref(v_opIdOf_2284_);
if (lean_obj_tag(v___x_2285_) == 1)
{
lean_object* v_val_2286_; lean_object* v___x_2288_; 
lean_dec_ref(v_op_2267_);
v_val_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v___x_2285_, 1);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v_val_2286_);
v___x_2288_ = v___x_2282_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_val_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
else
{
lean_object* v___x_2290_; 
lean_dec(v___x_2285_);
lean_del_object(v___x_2282_);
lean_inc_ref(v_op_2267_);
v___x_2290_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___f_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_n(v_a_2291_, 2);
lean_dec_ref_known(v___x_2290_, 1);
v___f_2292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2292_, 0, v_op_2267_);
lean_closure_set(v___f_2292_, 1, v_a_2291_);
v___x_2293_ = l_Lean_Meta_Grind_AC_acExt;
v___x_2294_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2293_, v___f_2292_, v_a_2268_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2294_, 0);
lean_dec(v_unused_2302_);
v___x_2296_ = v___x_2294_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v___x_2294_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_a_2291_);
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2291_);
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
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2291_);
v_a_2303_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2294_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2294_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_dec_ref(v_op_2267_);
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_op_2267_);
v_a_2312_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2279_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2279_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(lean_object* v_op_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_Grind_AC_getOpId_x3f(v_op_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec(v_a_2321_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f(lean_object* v_e_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v___y_2347_; uint8_t v___x_2380_; 
v___x_2380_ = l_Lean_Expr_isApp(v_e_2333_);
if (v___x_2380_ == 0)
{
v___y_2347_ = v___x_2380_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = l_Lean_Expr_appFn_x21(v_e_2333_);
v___x_2382_ = l_Lean_Expr_isApp(v___x_2381_);
lean_dec_ref(v___x_2381_);
v___y_2347_ = v___x_2382_;
goto v___jp_2346_;
}
v___jp_2346_:
{
if (v___y_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_Grind_AC_getOp(v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2371_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2371_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2371_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; uint8_t v___x_2359_; 
v___x_2355_ = l_Lean_Expr_appFn_x21(v_e_2333_);
v___x_2356_ = l_Lean_Expr_appFn_x21(v___x_2355_);
v___x_2357_ = lean_ptr_addr(v___x_2356_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = lean_ptr_addr(v_a_2351_);
lean_dec(v_a_2351_);
v___x_2359_ = lean_usize_dec_eq(v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref(v___x_2355_);
v___x_2360_ = lean_box(0);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2360_);
v___x_2362_ = v___x_2353_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2364_ = l_Lean_Expr_appArg_x21(v___x_2355_);
lean_dec_ref(v___x_2355_);
v___x_2365_ = l_Lean_Expr_appArg_x21(v_e_2333_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2367_);
v___x_2369_ = v___x_2353_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2350_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2350_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isOp_x3f___boxed(lean_object* v_e_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_Grind_AC_isOp_x3f(v_e_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_e_2383_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative(lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2425_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2425_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2425_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_commInst_x3f_2414_; 
v_commInst_x3f_2414_ = lean_ctor_get(v_a_2410_, 7);
lean_inc(v_commInst_x3f_2414_);
lean_dec(v_a_2410_);
if (lean_obj_tag(v_commInst_x3f_2414_) == 0)
{
uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2415_ = 0;
v___x_2416_ = lean_box(v___x_2415_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2416_);
v___x_2418_ = v___x_2412_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
else
{
uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec_ref_known(v_commInst_x3f_2414_, 1);
v___x_2420_ = 1;
v___x_2421_ = lean_box(v___x_2420_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2421_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2409_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2409_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isCommutative___boxed(lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_Grind_AC_isCommutative(v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec(v_a_2434_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral(lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2475_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2475_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2475_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_neutralInst_x3f_2464_; 
v_neutralInst_x3f_2464_ = lean_ctor_get(v_a_2460_, 8);
lean_inc(v_neutralInst_x3f_2464_);
lean_dec(v_a_2460_);
if (lean_obj_tag(v_neutralInst_x3f_2464_) == 0)
{
uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2465_ = 0;
v___x_2466_ = lean_box(v___x_2465_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2466_);
v___x_2468_ = v___x_2462_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
else
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_dec_ref_known(v_neutralInst_x3f_2464_, 1);
v___x_2470_ = 1;
v___x_2471_ = lean_box(v___x_2470_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2471_);
v___x_2473_ = v___x_2462_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2459_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2459_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_hasNeutral___boxed(lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Grind_AC_hasNeutral(v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec(v_a_2484_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent(lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_Grind_AC_ACM_getStruct(v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2525_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2525_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2525_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_idempotentInst_x3f_2514_; 
v_idempotentInst_x3f_2514_ = lean_ctor_get(v_a_2510_, 6);
lean_inc(v_idempotentInst_x3f_2514_);
lean_dec(v_a_2510_);
if (lean_obj_tag(v_idempotentInst_x3f_2514_) == 0)
{
uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = 0;
v___x_2516_ = lean_box(v___x_2515_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2516_);
v___x_2518_ = v___x_2512_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec_ref_known(v_idempotentInst_x3f_2514_, 1);
v___x_2520_ = 1;
v___x_2521_ = lean_box(v___x_2520_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2521_);
v___x_2523_ = v___x_2512_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2509_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2509_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_isIdempotent___boxed(lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Meta_Grind_AC_isIdempotent(v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec(v_a_2534_);
return v_res_2546_;
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
