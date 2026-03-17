// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Core
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Inv import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.Ctor import Lean.Meta.Tactic.Grind.Beta import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Internalize import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_eagerReflBoolFalse;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_PendingSolverPropagations_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_DelayedTheoremInstance_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetParentsOf___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_copyParentsTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
uint64_t l_Lean_Meta_Grind_instHashableCongrKey___private__1(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqCongrKey___private__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isCongrRoot(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsInconsistent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 81, 119, 21, 241, 124, 41, 97)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "remove: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reinsert: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__5_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "curr: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parent: "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fn: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", parents: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_propagateBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fns: "};
static const lean_object* l_Lean_Meta_Grind_propagateBeta___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBeta___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__1;
static const lean_string_object l_Lean_Meta_Grind_propagateBeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", lams: "};
static const lean_object* l_Lean_Meta_Grind_propagateBeta___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBeta___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBeta___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBeta___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Inhabited"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 88, 86, 106, 191, 136, 33, 185)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 152, 115, 107, 166, 56, 116, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " new root "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "adding "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "after addEqStep, "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 244, 178, 10, 61, 92, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " are already in the same equivalence class"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 181, 250, 47, 64, 71, 92, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object* v_e_1_, uint8_t v_flippedNew_2_, lean_object* v_targetNew_x3f_3_, lean_object* v_proofNew_x3f_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_st_ref_get(v_a_5_);
lean_inc_ref(v_e_1_);
v___x_12_ = l_Lean_Meta_Grind_Goal_getENode(v___x_11_, v_e_1_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_self_14_; lean_object* v_next_15_; lean_object* v_root_16_; lean_object* v_congr_17_; lean_object* v_target_x3f_18_; lean_object* v_proof_x3f_19_; uint8_t v_flipped_20_; lean_object* v_size_21_; uint8_t v_interpreted_22_; uint8_t v_ctor_23_; uint8_t v_hasLambdas_24_; uint8_t v_heqProofs_25_; lean_object* v_idx_26_; lean_object* v_generation_27_; lean_object* v_mt_28_; lean_object* v_sTerms_29_; uint8_t v_funCC_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_53_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v___x_12_);
v_self_14_ = lean_ctor_get(v_a_13_, 0);
v_next_15_ = lean_ctor_get(v_a_13_, 1);
v_root_16_ = lean_ctor_get(v_a_13_, 2);
v_congr_17_ = lean_ctor_get(v_a_13_, 3);
v_target_x3f_18_ = lean_ctor_get(v_a_13_, 4);
v_proof_x3f_19_ = lean_ctor_get(v_a_13_, 5);
v_flipped_20_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11);
v_size_21_ = lean_ctor_get(v_a_13_, 6);
v_interpreted_22_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 1);
v_ctor_23_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 2);
v_hasLambdas_24_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 3);
v_heqProofs_25_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 4);
v_idx_26_ = lean_ctor_get(v_a_13_, 7);
v_generation_27_ = lean_ctor_get(v_a_13_, 8);
v_mt_28_ = lean_ctor_get(v_a_13_, 9);
v_sTerms_29_ = lean_ctor_get(v_a_13_, 10);
v_funCC_30_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 5);
v_isSharedCheck_53_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_53_ == 0)
{
v___x_32_ = v_a_13_;
v_isShared_33_ = v_isSharedCheck_53_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_sTerms_29_);
lean_inc(v_mt_28_);
lean_inc(v_generation_27_);
lean_inc(v_idx_26_);
lean_inc(v_size_21_);
lean_inc(v_proof_x3f_19_);
lean_inc(v_target_x3f_18_);
lean_inc(v_congr_17_);
lean_inc(v_root_16_);
lean_inc(v_next_15_);
lean_inc(v_self_14_);
lean_dec(v_a_13_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_53_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___y_35_; 
if (lean_obj_tag(v_target_x3f_18_) == 1)
{
lean_object* v_val_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_52_; 
v_val_40_ = lean_ctor_get(v_target_x3f_18_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v_target_x3f_18_);
if (v_isSharedCheck_52_ == 0)
{
v___x_42_ = v_target_x3f_18_;
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_val_40_);
lean_dec(v_target_x3f_18_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___y_45_; 
if (v_flipped_20_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = 1;
v___y_45_ = v___x_50_;
goto v___jp_44_;
}
else
{
uint8_t v___x_51_; 
v___x_51_ = 0;
v___y_45_ = v___x_51_;
goto v___jp_44_;
}
v___jp_44_:
{
lean_object* v___x_47_; 
lean_inc_ref(v_e_1_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v_e_1_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_e_1_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_val_40_, v___y_45_, v___x_47_, v_proof_x3f_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_dec_ref(v___x_48_);
v___y_35_ = v_a_5_;
goto v___jp_34_;
}
else
{
lean_del_object(v___x_32_);
lean_dec(v_sTerms_29_);
lean_dec(v_mt_28_);
lean_dec(v_generation_27_);
lean_dec(v_idx_26_);
lean_dec(v_size_21_);
lean_dec_ref(v_congr_17_);
lean_dec_ref(v_root_16_);
lean_dec_ref(v_next_15_);
lean_dec_ref(v_self_14_);
lean_dec(v_proofNew_x3f_4_);
lean_dec(v_targetNew_x3f_3_);
lean_dec_ref(v_e_1_);
return v___x_48_;
}
}
}
}
}
else
{
lean_dec(v_proof_x3f_19_);
lean_dec(v_target_x3f_18_);
v___y_35_ = v_a_5_;
goto v___jp_34_;
}
v___jp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v___x_32_, 4, v_targetNew_x3f_3_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_self_14_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_next_15_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v_root_16_);
lean_ctor_set(v_reuseFailAlloc_39_, 3, v_congr_17_);
lean_ctor_set(v_reuseFailAlloc_39_, 4, v_targetNew_x3f_3_);
lean_ctor_set(v_reuseFailAlloc_39_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v_reuseFailAlloc_39_, 6, v_size_21_);
lean_ctor_set(v_reuseFailAlloc_39_, 7, v_idx_26_);
lean_ctor_set(v_reuseFailAlloc_39_, 8, v_generation_27_);
lean_ctor_set(v_reuseFailAlloc_39_, 9, v_mt_28_);
lean_ctor_set(v_reuseFailAlloc_39_, 10, v_sTerms_29_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 1, v_interpreted_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 2, v_ctor_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 3, v_hasLambdas_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 4, v_heqProofs_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 5, v_funCC_30_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*11, v_flippedNew_2_);
v___x_38_ = l_Lean_Meta_Grind_setENode___redArg(v_e_1_, v___x_37_, v___y_35_);
return v___x_38_;
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec(v_proofNew_x3f_4_);
lean_dec(v_targetNew_x3f_3_);
lean_dec_ref(v_e_1_);
v_a_54_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_12_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_12_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* v_e_62_, lean_object* v_flippedNew_63_, lean_object* v_targetNew_x3f_64_, lean_object* v_proofNew_x3f_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
uint8_t v_flippedNew_boxed_72_; lean_object* v_res_73_; 
v_flippedNew_boxed_72_ = lean_unbox(v_flippedNew_63_);
v_res_73_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_62_, v_flippedNew_boxed_72_, v_targetNew_x3f_64_, v_proofNew_x3f_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* v_e_74_, uint8_t v_flippedNew_75_, lean_object* v_targetNew_x3f_76_, lean_object* v_proofNew_x3f_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_74_, v_flippedNew_75_, v_targetNew_x3f_76_, v_proofNew_x3f_77_, v_a_78_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* v_e_90_, lean_object* v_flippedNew_91_, lean_object* v_targetNew_x3f_92_, lean_object* v_proofNew_x3f_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
uint8_t v_flippedNew_boxed_105_; lean_object* v_res_106_; 
v_flippedNew_boxed_105_ = lean_unbox(v_flippedNew_91_);
v_res_106_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(v_e_90_, v_flippedNew_boxed_105_, v_targetNew_x3f_92_, v_proofNew_x3f_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* v_e_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = 0;
v___x_115_ = lean_box(0);
v___x_116_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_107_, v___x_114_, v___x_115_, v___x_115_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* v_e_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_125_, v_a_126_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(v_e_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec(v_a_139_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* v_parent_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Expr_isApp(v_parent_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = l_Lean_Expr_isArrow(v_parent_151_);
return v___x_153_;
}
else
{
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_154_);
lean_dec_ref(v_parent_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_options_163_; uint8_t v_hasTrace_164_; 
v_options_163_ = lean_ctor_get(v___y_161_, 2);
v_hasTrace_164_ = lean_ctor_get_uint8(v_options_163_, sizeof(void*)*1);
if (v_hasTrace_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_cls_160_);
v___x_165_ = lean_box(v_hasTrace_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_inheritedTraceOptions_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_inheritedTraceOptions_167_ = lean_ctor_get(v___y_161_, 13);
v___x_168_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_169_ = l_Lean_Name_append(v___x_168_, v_cls_160_);
v___x_170_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_167_, v_options_163_, v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = lean_box(v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_173_, v___y_174_);
lean_dec_ref(v___y_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_177_, v___y_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec(v___y_191_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(lean_object* v_msgData_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; lean_object* v_env_210_; lean_object* v___x_211_; lean_object* v_mctx_212_; lean_object* v_lctx_213_; lean_object* v_options_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_209_ = lean_st_ref_get(v___y_207_);
v_env_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_env_210_);
lean_dec(v___x_209_);
v___x_211_ = lean_st_ref_get(v___y_205_);
v_mctx_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_211_);
v_lctx_213_ = lean_ctor_get(v___y_204_, 2);
v_options_214_ = lean_ctor_get(v___y_206_, 2);
lean_inc_ref(v_options_214_);
lean_inc_ref(v_lctx_213_);
v___x_215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_215_, 0, v_env_210_);
lean_ctor_set(v___x_215_, 1, v_mctx_212_);
lean_ctor_set(v___x_215_, 2, v_lctx_213_);
lean_ctor_set(v___x_215_, 3, v_options_214_);
v___x_216_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msgData_203_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3___boxed(lean_object* v_msgData_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(v_msgData_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_224_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_225_; double v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_float_of_nat(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_cls_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_ref_237_; lean_object* v___x_238_; lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_283_; 
v_ref_237_ = lean_ctor_get(v___y_234_, 5);
v___x_238_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_spec__3(v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_283_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v_traceState_244_; lean_object* v_env_245_; lean_object* v_nextMacroScope_246_; lean_object* v_ngen_247_; lean_object* v_auxDeclNGen_248_; lean_object* v_cache_249_; lean_object* v_messages_250_; lean_object* v_infoState_251_; lean_object* v_snapshotTasks_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_282_; 
v___x_243_ = lean_st_ref_take(v___y_235_);
v_traceState_244_ = lean_ctor_get(v___x_243_, 4);
v_env_245_ = lean_ctor_get(v___x_243_, 0);
v_nextMacroScope_246_ = lean_ctor_get(v___x_243_, 1);
v_ngen_247_ = lean_ctor_get(v___x_243_, 2);
v_auxDeclNGen_248_ = lean_ctor_get(v___x_243_, 3);
v_cache_249_ = lean_ctor_get(v___x_243_, 5);
v_messages_250_ = lean_ctor_get(v___x_243_, 6);
v_infoState_251_ = lean_ctor_get(v___x_243_, 7);
v_snapshotTasks_252_ = lean_ctor_get(v___x_243_, 8);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_282_ == 0)
{
v___x_254_ = v___x_243_;
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snapshotTasks_252_);
lean_inc(v_infoState_251_);
lean_inc(v_messages_250_);
lean_inc(v_cache_249_);
lean_inc(v_traceState_244_);
lean_inc(v_auxDeclNGen_248_);
lean_inc(v_ngen_247_);
lean_inc(v_nextMacroScope_246_);
lean_inc(v_env_245_);
lean_dec(v___x_243_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint64_t v_tid_256_; lean_object* v_traces_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_281_; 
v_tid_256_ = lean_ctor_get_uint64(v_traceState_244_, sizeof(void*)*1);
v_traces_257_ = lean_ctor_get(v_traceState_244_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v_traceState_244_);
if (v_isSharedCheck_281_ == 0)
{
v___x_259_ = v_traceState_244_;
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_traces_257_);
lean_dec(v_traceState_244_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; double v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_261_ = lean_box(0);
v___x_262_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0);
v___x_263_ = 0;
v___x_264_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1));
v___x_265_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_265_, 0, v_cls_230_);
lean_ctor_set(v___x_265_, 1, v___x_261_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
lean_ctor_set_float(v___x_265_, sizeof(void*)*3, v___x_262_);
lean_ctor_set_float(v___x_265_, sizeof(void*)*3 + 8, v___x_262_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*3 + 16, v___x_263_);
v___x_266_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2));
v___x_267_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v_a_239_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc(v_ref_237_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_237_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_PersistentArray_push___redArg(v_traces_257_, v___x_268_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_269_);
v___x_271_ = v___x_259_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_269_);
lean_ctor_set_uint64(v_reuseFailAlloc_280_, sizeof(void*)*1, v_tid_256_);
v___x_271_ = v_reuseFailAlloc_280_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 4, v___x_271_);
v___x_273_ = v___x_254_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_env_245_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_nextMacroScope_246_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_ngen_247_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_auxDeclNGen_248_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_cache_249_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_messages_250_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_infoState_251_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_snapshotTasks_252_);
v___x_273_ = v_reuseFailAlloc_279_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = lean_st_ref_set(v___y_235_, v___x_273_);
v___x_275_ = lean_box(0);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_275_);
v___x_277_ = v___x_241_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_cls_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_cls_284_, v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(lean_object* v___x_292_, lean_object* v_xs_293_, lean_object* v_v_294_, lean_object* v_i_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v_xs_293_);
v___x_297_ = lean_nat_dec_lt(v_i_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v_i_295_);
lean_dec_ref(v_v_294_);
lean_dec_ref(v___x_292_);
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_xs_293_, v_i_295_);
lean_inc_ref(v_v_294_);
lean_inc(v___x_299_);
lean_inc_ref(v___x_292_);
v___x_300_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_292_, v___x_299_, v_v_294_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_295_, v___x_301_);
lean_dec(v_i_295_);
v_i_295_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_v_294_);
lean_dec_ref(v___x_292_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_i_295_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v___x_305_, lean_object* v_xs_306_, lean_object* v_v_307_, lean_object* v_i_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(v___x_305_, v_xs_306_, v_v_307_, v_i_308_);
lean_dec_ref(v_xs_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(lean_object* v___x_310_, lean_object* v_xs_311_, lean_object* v_v_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2_spec__6(v___x_310_, v_xs_311_, v_v_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2___boxed(lean_object* v___x_315_, lean_object* v_xs_316_, lean_object* v_v_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(v___x_315_, v_xs_316_, v_v_317_);
lean_dec_ref(v_xs_316_);
return v_res_318_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; 
v___x_319_ = ((size_t)5ULL);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_shift_left(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; 
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0);
v___x_324_ = lean_usize_sub(v___x_323_, v___x_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_325_, lean_object* v_x_326_, size_t v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_es_329_; lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_j_334_; lean_object* v_entry_335_; 
v_es_329_ = lean_ctor_get(v_x_326_, 0);
v___x_330_ = lean_box(2);
v___x_331_ = ((size_t)5ULL);
v___x_332_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_333_ = lean_usize_land(v_x_327_, v___x_332_);
v_j_334_ = lean_usize_to_nat(v___x_333_);
v_entry_335_ = lean_array_get(v___x_330_, v_es_329_, v_j_334_);
switch(lean_obj_tag(v_entry_335_))
{
case 0:
{
lean_object* v_key_336_; uint8_t v___x_337_; 
v_key_336_ = lean_ctor_get(v_entry_335_, 0);
lean_inc(v_key_336_);
lean_dec_ref(v_entry_335_);
v___x_337_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_325_, v_x_328_, v_key_336_);
if (v___x_337_ == 0)
{
lean_dec(v_j_334_);
return v_x_326_;
}
else
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_345_; 
lean_inc_ref(v_es_329_);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; 
v_unused_346_ = lean_ctor_get(v_x_326_, 0);
lean_dec(v_unused_346_);
v___x_339_ = v_x_326_;
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_x_326_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_345_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_array_set(v_es_329_, v_j_334_, v___x_330_);
lean_dec(v_j_334_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
case 1:
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_380_; 
lean_inc_ref(v_es_329_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_x_326_, 0);
lean_dec(v_unused_381_);
v___x_348_ = v_x_326_;
v_isShared_349_ = v_isSharedCheck_380_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_x_326_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_380_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_node_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_379_; 
v_node_350_ = lean_ctor_get(v_entry_335_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_entry_335_);
if (v_isSharedCheck_379_ == 0)
{
v___x_352_ = v_entry_335_;
v_isShared_353_ = v_isSharedCheck_379_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_node_350_);
lean_dec(v_entry_335_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_379_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_entries_354_; size_t v___x_355_; lean_object* v_newNode_356_; lean_object* v___x_357_; 
v_entries_354_ = lean_array_set(v_es_329_, v_j_334_, v___x_330_);
v___x_355_ = lean_usize_shift_right(v_x_327_, v___x_331_);
v_newNode_356_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_325_, v_node_350_, v___x_355_, v_x_328_);
lean_inc_ref(v_newNode_356_);
v___x_357_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v_newNode_356_);
v___x_359_ = v___x_352_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_newNode_356_);
v___x_359_ = v_reuseFailAlloc_364_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_array_set(v_entries_354_, v_j_334_, v___x_359_);
lean_dec(v_j_334_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_360_);
v___x_362_ = v___x_348_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_val_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_newNode_356_);
lean_del_object(v___x_352_);
v_val_365_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_val_365_);
lean_dec_ref(v___x_357_);
v_fst_366_ = lean_ctor_get(v_val_365_, 0);
v_snd_367_ = lean_ctor_get(v_val_365_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_val_365_);
if (v_isSharedCheck_378_ == 0)
{
v___x_369_ = v_val_365_;
v_isShared_370_ = v_isSharedCheck_378_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_367_);
lean_inc(v_fst_366_);
lean_dec(v_val_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_378_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_fst_366_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_snd_367_);
v___x_372_ = v_reuseFailAlloc_377_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_array_set(v_entries_354_, v_j_334_, v___x_372_);
lean_dec(v_j_334_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_373_);
v___x_375_ = v___x_348_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_334_);
lean_dec_ref(v_x_328_);
lean_dec_ref(v___x_325_);
return v_x_326_;
}
}
}
else
{
lean_object* v_ks_382_; lean_object* v_vs_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_397_; 
v_ks_382_ = lean_ctor_get(v_x_326_, 0);
v_vs_383_ = lean_ctor_get(v_x_326_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_397_ == 0)
{
v___x_385_ = v_x_326_;
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_vs_383_);
lean_inc(v_ks_382_);
lean_dec(v_x_326_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_397_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__2(v___x_325_, v_ks_382_, v_x_328_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_389_; 
if (v_isShared_386_ == 0)
{
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_ks_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_vs_383_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v_val_391_; lean_object* v_keys_x27_392_; lean_object* v_vals_x27_393_; lean_object* v___x_395_; 
v_val_391_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_val_391_);
lean_dec_ref(v___x_387_);
lean_inc(v_val_391_);
v_keys_x27_392_ = l_Array_eraseIdx___redArg(v_ks_382_, v_val_391_);
v_vals_x27_393_ = l_Array_eraseIdx___redArg(v_vs_383_, v_val_391_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_vals_x27_393_);
lean_ctor_set(v___x_385_, 0, v_keys_x27_392_);
v___x_395_ = v___x_385_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_keys_x27_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_vals_x27_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
size_t v_x_27247__boxed_402_; lean_object* v_res_403_; 
v_x_27247__boxed_402_ = lean_unbox_usize(v_x_400_);
lean_dec(v_x_400_);
v_res_403_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_398_, v_x_399_, v_x_27247__boxed_402_, v_x_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
uint64_t v___x_407_; size_t v_h_408_; lean_object* v___x_409_; 
lean_inc_ref(v_x_406_);
lean_inc_ref(v___x_404_);
v___x_407_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_404_, v_x_406_);
v_h_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_404_, v_x_405_, v_h_408_, v_x_406_);
return v___x_409_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__4));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(lean_object* v_as_x27_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
if (lean_obj_tag(v_as_x27_420_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_b_421_);
return v___x_433_;
}
else
{
lean_object* v_head_434_; lean_object* v_tail_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_507_; 
v_head_434_ = lean_ctor_get(v_as_x27_420_, 0);
v_tail_435_ = lean_ctor_get(v_as_x27_420_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_as_x27_420_);
if (v_isSharedCheck_507_ == 0)
{
v___x_437_ = v_as_x27_420_;
v_isShared_438_ = v_isSharedCheck_507_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_tail_435_);
lean_inc(v_head_434_);
lean_dec(v_as_x27_420_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_507_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___y_441_; uint8_t v_a_482_; uint8_t v___x_495_; 
v___x_439_ = lean_box(0);
v___x_495_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_434_);
if (v___x_495_ == 0)
{
v_a_482_ = v___x_495_;
goto v___jp_481_;
}
else
{
lean_object* v___x_496_; 
lean_inc(v_head_434_);
v___x_496_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_434_, v___y_422_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; uint8_t v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v___x_498_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
v_a_482_ = v___x_498_;
goto v___jp_481_;
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_del_object(v___x_437_);
lean_dec(v_tail_435_);
lean_dec(v_head_434_);
v_a_499_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_496_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_496_);
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
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v_toGoalState_443_; lean_object* v_mvarId_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_480_; 
v___x_442_ = lean_st_ref_take(v___y_441_);
v_toGoalState_443_ = lean_ctor_get(v___x_442_, 0);
v_mvarId_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_480_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_480_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_mvarId_444_);
lean_inc(v_toGoalState_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_480_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_nextDeclIdx_448_; lean_object* v_canon_449_; lean_object* v_enodeMap_450_; lean_object* v_exprs_451_; lean_object* v_parents_452_; lean_object* v_congrTable_453_; lean_object* v_appMap_454_; lean_object* v_indicesFound_455_; lean_object* v_newFacts_456_; uint8_t v_inconsistent_457_; lean_object* v_nextIdx_458_; lean_object* v_newRawFacts_459_; lean_object* v_facts_460_; lean_object* v_extThms_461_; lean_object* v_ematch_462_; lean_object* v_inj_463_; lean_object* v_split_464_; lean_object* v_clean_465_; lean_object* v_sstates_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_479_; 
v_nextDeclIdx_448_ = lean_ctor_get(v_toGoalState_443_, 0);
v_canon_449_ = lean_ctor_get(v_toGoalState_443_, 1);
v_enodeMap_450_ = lean_ctor_get(v_toGoalState_443_, 2);
v_exprs_451_ = lean_ctor_get(v_toGoalState_443_, 3);
v_parents_452_ = lean_ctor_get(v_toGoalState_443_, 4);
v_congrTable_453_ = lean_ctor_get(v_toGoalState_443_, 5);
v_appMap_454_ = lean_ctor_get(v_toGoalState_443_, 6);
v_indicesFound_455_ = lean_ctor_get(v_toGoalState_443_, 7);
v_newFacts_456_ = lean_ctor_get(v_toGoalState_443_, 8);
v_inconsistent_457_ = lean_ctor_get_uint8(v_toGoalState_443_, sizeof(void*)*18);
v_nextIdx_458_ = lean_ctor_get(v_toGoalState_443_, 9);
v_newRawFacts_459_ = lean_ctor_get(v_toGoalState_443_, 10);
v_facts_460_ = lean_ctor_get(v_toGoalState_443_, 11);
v_extThms_461_ = lean_ctor_get(v_toGoalState_443_, 12);
v_ematch_462_ = lean_ctor_get(v_toGoalState_443_, 13);
v_inj_463_ = lean_ctor_get(v_toGoalState_443_, 14);
v_split_464_ = lean_ctor_get(v_toGoalState_443_, 15);
v_clean_465_ = lean_ctor_get(v_toGoalState_443_, 16);
v_sstates_466_ = lean_ctor_get(v_toGoalState_443_, 17);
v_isSharedCheck_479_ = !lean_is_exclusive(v_toGoalState_443_);
if (v_isSharedCheck_479_ == 0)
{
v___x_468_ = v_toGoalState_443_;
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_sstates_466_);
lean_inc(v_clean_465_);
lean_inc(v_split_464_);
lean_inc(v_inj_463_);
lean_inc(v_ematch_462_);
lean_inc(v_extThms_461_);
lean_inc(v_facts_460_);
lean_inc(v_newRawFacts_459_);
lean_inc(v_nextIdx_458_);
lean_inc(v_newFacts_456_);
lean_inc(v_indicesFound_455_);
lean_inc(v_appMap_454_);
lean_inc(v_congrTable_453_);
lean_inc(v_parents_452_);
lean_inc(v_exprs_451_);
lean_inc(v_enodeMap_450_);
lean_inc(v_canon_449_);
lean_inc(v_nextDeclIdx_448_);
lean_dec(v_toGoalState_443_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_479_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_inc_ref(v_enodeMap_450_);
v___x_470_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_450_, v_congrTable_453_, v_head_434_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 5, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_nextDeclIdx_448_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_canon_449_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_enodeMap_450_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_exprs_451_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_parents_452_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_appMap_454_);
lean_ctor_set(v_reuseFailAlloc_478_, 7, v_indicesFound_455_);
lean_ctor_set(v_reuseFailAlloc_478_, 8, v_newFacts_456_);
lean_ctor_set(v_reuseFailAlloc_478_, 9, v_nextIdx_458_);
lean_ctor_set(v_reuseFailAlloc_478_, 10, v_newRawFacts_459_);
lean_ctor_set(v_reuseFailAlloc_478_, 11, v_facts_460_);
lean_ctor_set(v_reuseFailAlloc_478_, 12, v_extThms_461_);
lean_ctor_set(v_reuseFailAlloc_478_, 13, v_ematch_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 14, v_inj_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 15, v_split_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 16, v_clean_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 17, v_sstates_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*18, v_inconsistent_457_);
v___x_472_ = v_reuseFailAlloc_478_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_472_);
v___x_474_ = v___x_446_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_mvarId_444_);
v___x_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_st_ref_set(v___y_441_, v___x_474_);
v_as_x27_420_ = v_tail_435_;
v_b_421_ = v___x_439_;
goto _start;
}
}
}
}
}
v___jp_481_:
{
if (v_a_482_ == 0)
{
lean_del_object(v___x_437_);
lean_dec(v_head_434_);
v_as_x27_420_ = v_tail_435_;
v_b_421_ = v___x_439_;
goto _start;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_a_486_; uint8_t v___x_487_; 
v___x_484_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3));
v___x_485_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_484_, v___y_430_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v___x_487_ = lean_unbox(v_a_486_);
lean_dec(v_a_486_);
if (v___x_487_ == 0)
{
lean_del_object(v___x_437_);
v___y_441_ = v___y_422_;
goto v___jp_440_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_updateLastTag(v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec_ref(v___x_488_);
v___x_489_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__5);
lean_inc(v_head_434_);
v___x_490_ = l_Lean_MessageData_ofExpr(v_head_434_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 7);
lean_ctor_set(v___x_437_, 1, v___x_490_);
lean_ctor_set(v___x_437_, 0, v___x_489_);
v___x_492_ = v___x_437_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_494_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_484_, v___x_492_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_dec_ref(v___x_493_);
v___y_441_ = v___y_422_;
goto v___jp_440_;
}
else
{
lean_dec(v_tail_435_);
lean_dec(v_head_434_);
return v___x_493_;
}
}
}
else
{
lean_del_object(v___x_437_);
lean_dec(v_tail_435_);
lean_dec(v_head_434_);
return v___x_488_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___boxed(lean_object* v_as_x27_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(v_as_x27_508_, v_b_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec(v___y_510_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_getParents___redArg(v_root_522_, v_a_523_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_535_);
v___x_537_ = lean_box(0);
v___x_538_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(v___x_536_, v___x_537_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v___x_538_, 0);
lean_dec(v_unused_546_);
v___x_540_ = v___x_538_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_dec(v___x_538_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_a_535_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_535_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_535_);
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_root_555_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_568_, lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_568_, v_x_570_, v_x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_cls_573_, lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_cls_573_, v_msg_574_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_cls_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_cls_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v___y_589_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(lean_object* v_as_601_, lean_object* v_as_x27_602_, lean_object* v_b_603_, lean_object* v_a_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg(v_as_x27_602_, v_b_603_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___boxed(lean_object* v_as_617_, lean_object* v_as_x27_618_, lean_object* v_b_619_, lean_object* v_a_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3(v_as_617_, v_as_x27_618_, v_b_619_, v_a_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v_as_617_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_633_, lean_object* v_00_u03b2_634_, lean_object* v_x_635_, size_t v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_633_, v_x_635_, v_x_636_, v_x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_639_, lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
size_t v_x_27736__boxed_644_; lean_object* v_res_645_; 
v_x_27736__boxed_644_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_res_645_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_639_, v_00_u03b2_640_, v_x_641_, v_x_27736__boxed_644_, v_x_643_);
return v_res_645_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
if (lean_obj_tag(v_as_x27_649_) == 0)
{
lean_object* v___x_662_; 
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_b_650_);
return v___x_662_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_708_; 
v_head_663_ = lean_ctor_get(v_as_x27_649_, 0);
v_tail_664_ = lean_ctor_get(v_as_x27_649_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_as_x27_649_);
if (v_isSharedCheck_708_ == 0)
{
v___x_666_ = v_as_x27_649_;
v_isShared_667_ = v_isSharedCheck_708_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_tail_664_);
lean_inc(v_head_663_);
lean_dec(v_as_x27_649_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_708_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; uint8_t v_a_683_; uint8_t v___x_696_; 
v___x_668_ = lean_box(0);
v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_663_);
if (v___x_696_ == 0)
{
v_a_683_ = v___x_696_;
goto v___jp_682_;
}
else
{
lean_object* v___x_697_; 
lean_inc(v_head_663_);
v___x_697_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_663_, v___y_651_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; uint8_t v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___x_699_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
v_a_683_ = v___x_699_;
goto v___jp_682_;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_666_);
lean_dec(v_tail_664_);
lean_dec(v_head_663_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
v_a_700_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_697_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_697_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
v___jp_669_:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Grind_addCongrTable(v_head_663_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref(v___x_680_);
v_as_x27_649_ = v_tail_664_;
v_b_650_ = v___x_668_;
goto _start;
}
else
{
lean_dec(v_tail_664_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v___x_680_;
}
}
v___jp_682_:
{
if (v_a_683_ == 0)
{
lean_del_object(v___x_666_);
lean_dec(v_head_663_);
v_as_x27_649_ = v_tail_664_;
v_b_650_ = v___x_668_;
goto _start;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_a_687_; uint8_t v___x_688_; 
v___x_685_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__3));
v___x_686_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_685_, v___y_659_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_unbox(v_a_687_);
lean_dec(v_a_687_);
if (v___x_688_ == 0)
{
lean_del_object(v___x_666_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___y_670_ = v___y_651_;
v___y_671_ = v___y_652_;
v___y_672_ = v___y_653_;
v___y_673_ = v___y_654_;
v___y_674_ = v___y_655_;
v___y_675_ = v___y_656_;
v___y_676_ = v___y_657_;
v___y_677_ = v___y_658_;
v___y_678_ = v___y_659_;
v___y_679_ = v___y_660_;
goto v___jp_669_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Grind_updateLastTag(v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec_ref(v___x_689_);
v___x_690_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_663_);
v___x_691_ = l_Lean_MessageData_ofExpr(v_head_663_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 7);
lean_ctor_set(v___x_666_, 1, v___x_691_);
lean_ctor_set(v___x_666_, 0, v___x_690_);
v___x_693_ = v___x_666_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_685_, v___x_693_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref(v___x_694_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
v___y_670_ = v___y_651_;
v___y_671_ = v___y_652_;
v___y_672_ = v___y_653_;
v___y_673_ = v___y_654_;
v___y_674_ = v___y_655_;
v___y_675_ = v___y_656_;
v___y_676_ = v___y_657_;
v___y_677_ = v___y_658_;
v___y_678_ = v___y_659_;
v___y_679_ = v___y_660_;
goto v___jp_669_;
}
else
{
lean_dec(v_tail_664_);
lean_dec(v_head_663_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v___x_694_;
}
}
}
else
{
lean_del_object(v___x_666_);
lean_dec(v_tail_664_);
lean_dec(v_head_663_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v___x_689_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_709_, v_b_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_723_);
v___x_736_ = lean_box(0);
v___x_737_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_735_, v___x_736_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_745_);
v___x_739_ = v___x_737_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_dec(v___x_737_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_736_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_736_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec(v_a_747_);
lean_dec(v_parents_746_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_759_, lean_object* v_as_x27_760_, lean_object* v_b_761_, lean_object* v_a_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_760_, v_b_761_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_775_, lean_object* v_as_x27_776_, lean_object* v_b_777_, lean_object* v_a_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_775_, v_as_x27_776_, v_b_777_, v_a_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v_as_775_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_791_, lean_object* v_i_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_keys_791_);
v___x_795_ = lean_nat_dec_lt(v_i_792_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v_i_792_);
return v___x_795_;
}
else
{
lean_object* v_k_x27_796_; uint8_t v___x_797_; 
v_k_x27_796_ = lean_array_fget_borrowed(v_keys_791_, v_i_792_);
v___x_797_ = l_Lean_instBEqMVarId_beq(v_k_793_, v_k_x27_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_i_792_, v___x_798_);
lean_dec(v_i_792_);
v_i_792_ = v___x_799_;
goto _start;
}
else
{
lean_dec(v_i_792_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_801_, lean_object* v_i_802_, lean_object* v_k_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_801_, v_i_802_, v_k_803_);
lean_dec(v_k_803_);
lean_dec_ref(v_keys_801_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_806_, size_t v_x_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
lean_object* v_es_809_; lean_object* v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; lean_object* v_j_814_; lean_object* v___x_815_; 
v_es_809_ = lean_ctor_get(v_x_806_, 0);
lean_inc_ref(v_es_809_);
lean_dec_ref(v_x_806_);
v___x_810_ = lean_box(2);
v___x_811_ = ((size_t)5ULL);
v___x_812_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_813_ = lean_usize_land(v_x_807_, v___x_812_);
v_j_814_ = lean_usize_to_nat(v___x_813_);
v___x_815_ = lean_array_get(v___x_810_, v_es_809_, v_j_814_);
lean_dec(v_j_814_);
lean_dec_ref(v_es_809_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_key_816_; uint8_t v___x_817_; 
v_key_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_key_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Lean_instBEqMVarId_beq(v_x_808_, v_key_816_);
lean_dec(v_key_816_);
return v___x_817_;
}
case 1:
{
lean_object* v_node_818_; size_t v___x_819_; 
v_node_818_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_node_818_);
lean_dec_ref(v___x_815_);
v___x_819_ = lean_usize_shift_right(v_x_807_, v___x_811_);
v_x_806_ = v_node_818_;
v_x_807_ = v___x_819_;
goto _start;
}
default: 
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
else
{
lean_object* v_ks_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_ks_822_ = lean_ctor_get(v_x_806_, 0);
lean_inc_ref(v_ks_822_);
lean_dec_ref(v_x_806_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_822_, v___x_823_, v_x_808_);
lean_dec_ref(v_ks_822_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_10287__boxed_828_; uint8_t v_res_829_; lean_object* v_r_830_; 
v_x_10287__boxed_828_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_res_829_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_825_, v_x_10287__boxed_828_, v_x_827_);
lean_dec(v_x_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint64_t v___x_833_; size_t v___x_834_; uint8_t v___x_835_; 
v___x_833_ = l_Lean_instHashableMVarId_hash(v_x_832_);
v___x_834_ = lean_uint64_to_usize(v___x_833_);
v___x_835_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_831_, v___x_834_, v_x_832_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_836_, v_x_837_);
lean_dec(v_x_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; lean_object* v_mctx_844_; lean_object* v_eAssignment_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_843_ = lean_st_ref_get(v___y_841_);
v_mctx_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc_ref(v_mctx_844_);
lean_dec(v___x_843_);
v_eAssignment_845_ = lean_ctor_get(v_mctx_844_, 7);
lean_inc_ref(v_eAssignment_845_);
lean_dec_ref(v_mctx_844_);
v___x_846_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_845_, v_mvarId_840_);
v___x_847_ = lean_box(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec(v_mvarId_849_);
return v_res_852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_871_ = l_Lean_mkConst(v___x_870_, v___x_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_mvarId_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_939_; 
v___x_883_ = lean_st_ref_get(v_a_872_);
v_mvarId_884_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_mvarId_884_);
lean_dec(v___x_883_);
v___x_885_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_884_, v_a_879_);
lean_dec(v_mvarId_884_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_939_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_939_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_939_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
uint8_t v___x_890_; 
v___x_890_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_del_object(v___x_888_);
v___x_891_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_876_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
lean_inc(v_a_881_);
lean_inc_ref(v_a_880_);
lean_inc(v_a_879_);
lean_inc_ref(v_a_878_);
lean_inc(v_a_877_);
lean_inc_ref(v_a_876_);
lean_inc(v_a_875_);
lean_inc_ref(v_a_874_);
lean_inc(v_a_873_);
lean_inc(v_a_872_);
v___x_893_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_892_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_876_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref(v___x_895_);
v___x_897_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_876_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_901_ = l_Lean_mkApp4(v___x_899_, v_a_896_, v_a_898_, v_a_894_, v___x_900_);
v___x_902_ = l_Lean_Meta_Grind_closeGoal(v___x_901_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_a_896_);
lean_dec(v_a_894_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
v_a_903_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_897_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_897_);
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
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_a_894_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
v_a_911_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_895_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_895_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
v_a_919_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_893_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_893_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
v_a_927_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_891_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_891_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec(v_a_872_);
v___x_935_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_935_);
v___x_937_ = v___x_888_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_952_, v___y_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v_mvarId_965_);
return v_res_977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_979_, v_x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
uint8_t v_res_985_; lean_object* v_r_986_; 
v_res_985_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_982_, v_x_983_, v_x_984_);
lean_dec(v_x_984_);
v_r_986_ = lean_box(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, size_t v_x_989_, lean_object* v_x_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_988_, v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_10602__boxed_996_; uint8_t v_res_997_; lean_object* v_r_998_; 
v_x_10602__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_992_, v_x_993_, v_x_10602__boxed_996_, v_x_995_);
lean_dec(v_x_995_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_heq_1002_, lean_object* v_i_1003_, lean_object* v_k_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_1000_, v_i_1003_, v_k_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_heq_1009_, lean_object* v_i_1010_, lean_object* v_k_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1006_, v_keys_1007_, v_vals_1008_, v_heq_1009_, v_i_1010_, v_k_1011_);
lean_dec(v_k_1011_);
lean_dec_ref(v_vals_1008_);
lean_dec_ref(v_keys_1007_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_1019_ = l_Lean_mkConst(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_1020_, lean_object* v_rhs_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1033_; 
lean_inc(v_a_1031_);
lean_inc_ref(v_a_1030_);
lean_inc(v_a_1029_);
lean_inc_ref(v_a_1028_);
lean_inc_ref(v_rhs_1021_);
lean_inc_ref(v_lhs_1020_);
v___x_1033_ = l_Lean_Meta_mkEq(v_lhs_1020_, v_rhs_1021_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref(v___x_1033_);
lean_inc(v_a_1031_);
lean_inc_ref(v_a_1030_);
lean_inc(v_a_1029_);
lean_inc_ref(v_a_1028_);
lean_inc(v_a_1027_);
lean_inc_ref(v_a_1026_);
lean_inc(v_a_1025_);
lean_inc_ref(v_a_1024_);
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
v___x_1035_ = lean_grind_mk_eq_proof(v_lhs_1020_, v_rhs_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
lean_inc(v_a_1031_);
lean_inc_ref(v_a_1030_);
lean_inc(v_a_1029_);
lean_inc_ref(v_a_1028_);
lean_inc(v_a_1034_);
v___x_1037_ = l_Lean_Meta_mkDecide(v_a_1034_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1026_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1042_ = l_Lean_Expr_appArg_x21(v_a_1038_);
lean_dec(v_a_1038_);
v___x_1043_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_1034_);
v___x_1044_ = l_Lean_mkApp3(v___x_1041_, v_a_1034_, v___x_1042_, v___x_1043_);
v___x_1045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1046_ = l_Lean_mkApp4(v___x_1045_, v_a_1034_, v_a_1040_, v___x_1044_, v_a_1036_);
v___x_1047_ = l_Lean_Meta_Grind_closeGoal(v___x_1046_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
return v___x_1047_;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_a_1038_);
lean_dec(v_a_1036_);
lean_dec(v_a_1034_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
v_a_1048_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1039_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1039_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_1036_);
lean_dec(v_a_1034_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
v_a_1056_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1037_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1037_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_a_1034_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
v_a_1064_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1035_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1035_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
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
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_rhs_1021_);
lean_dec_ref(v_lhs_1020_);
v_a_1072_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1033_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1033_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1080_, lean_object* v_rhs_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1080_, v_rhs_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1094_, lean_object* v_as_x27_1095_, lean_object* v_b_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
if (lean_obj_tag(v_as_x27_1095_) == 0)
{
lean_object* v___x_1108_; 
lean_dec(v___x_1094_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_b_1096_);
return v___x_1108_;
}
else
{
lean_object* v_head_1109_; lean_object* v_tail_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_head_1109_ = lean_ctor_get(v_as_x27_1095_, 0);
lean_inc(v_head_1109_);
v_tail_1110_ = lean_ctor_get(v_as_x27_1095_, 1);
lean_inc(v_tail_1110_);
lean_dec_ref(v_as_x27_1095_);
v___x_1111_ = lean_st_ref_get(v___y_1097_);
lean_inc(v_head_1109_);
v___x_1112_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1111_, v_head_1109_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v_self_1114_; lean_object* v_next_1115_; lean_object* v_root_1116_; lean_object* v_congr_1117_; lean_object* v_target_x3f_1118_; lean_object* v_proof_x3f_1119_; uint8_t v_flipped_1120_; lean_object* v_size_1121_; uint8_t v_interpreted_1122_; uint8_t v_ctor_1123_; uint8_t v_hasLambdas_1124_; uint8_t v_heqProofs_1125_; lean_object* v_idx_1126_; lean_object* v_generation_1127_; lean_object* v_mt_1128_; lean_object* v_sTerms_1129_; uint8_t v_funCC_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1143_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1112_);
v_self_1114_ = lean_ctor_get(v_a_1113_, 0);
v_next_1115_ = lean_ctor_get(v_a_1113_, 1);
v_root_1116_ = lean_ctor_get(v_a_1113_, 2);
v_congr_1117_ = lean_ctor_get(v_a_1113_, 3);
v_target_x3f_1118_ = lean_ctor_get(v_a_1113_, 4);
v_proof_x3f_1119_ = lean_ctor_get(v_a_1113_, 5);
v_flipped_1120_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11);
v_size_1121_ = lean_ctor_get(v_a_1113_, 6);
v_interpreted_1122_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11 + 1);
v_ctor_1123_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11 + 2);
v_hasLambdas_1124_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11 + 3);
v_heqProofs_1125_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11 + 4);
v_idx_1126_ = lean_ctor_get(v_a_1113_, 7);
v_generation_1127_ = lean_ctor_get(v_a_1113_, 8);
v_mt_1128_ = lean_ctor_get(v_a_1113_, 9);
v_sTerms_1129_ = lean_ctor_get(v_a_1113_, 10);
v_funCC_1130_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*11 + 5);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_a_1113_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1132_ = v_a_1113_;
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_sTerms_1129_);
lean_inc(v_mt_1128_);
lean_inc(v_generation_1127_);
lean_inc(v_idx_1126_);
lean_inc(v_size_1121_);
lean_inc(v_proof_x3f_1119_);
lean_inc(v_target_x3f_1118_);
lean_inc(v_congr_1117_);
lean_inc(v_root_1116_);
lean_inc(v_next_1115_);
lean_inc(v_self_1114_);
lean_dec(v_a_1113_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_nat_dec_lt(v_mt_1128_, v___x_1094_);
lean_dec(v_mt_1128_);
if (v___x_1135_ == 0)
{
lean_del_object(v___x_1132_);
lean_dec(v_sTerms_1129_);
lean_dec(v_generation_1127_);
lean_dec(v_idx_1126_);
lean_dec(v_size_1121_);
lean_dec(v_proof_x3f_1119_);
lean_dec(v_target_x3f_1118_);
lean_dec_ref(v_congr_1117_);
lean_dec_ref(v_root_1116_);
lean_dec_ref(v_next_1115_);
lean_dec_ref(v_self_1114_);
lean_dec(v_head_1109_);
v_as_x27_1095_ = v_tail_1110_;
v_b_1096_ = v___x_1134_;
goto _start;
}
else
{
lean_object* v___x_1138_; 
lean_inc(v___x_1094_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 9, v___x_1094_);
v___x_1138_ = v___x_1132_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_self_1114_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_next_1115_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_root_1116_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_congr_1117_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_target_x3f_1118_);
lean_ctor_set(v_reuseFailAlloc_1142_, 5, v_proof_x3f_1119_);
lean_ctor_set(v_reuseFailAlloc_1142_, 6, v_size_1121_);
lean_ctor_set(v_reuseFailAlloc_1142_, 7, v_idx_1126_);
lean_ctor_set(v_reuseFailAlloc_1142_, 8, v_generation_1127_);
lean_ctor_set(v_reuseFailAlloc_1142_, 9, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1142_, 10, v_sTerms_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11, v_flipped_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11 + 1, v_interpreted_1122_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11 + 2, v_ctor_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11 + 3, v_hasLambdas_1124_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11 + 4, v_heqProofs_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1142_, sizeof(void*)*11 + 5, v_funCC_1130_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
lean_inc(v_head_1109_);
v___x_1139_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1109_, v___x_1138_, v___y_1097_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; 
lean_dec_ref(v___x_1139_);
v___x_1140_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1109_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v_head_1109_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_dec_ref(v___x_1140_);
v_as_x27_1095_ = v_tail_1110_;
v_b_1096_ = v___x_1134_;
goto _start;
}
else
{
lean_dec(v_tail_1110_);
lean_dec(v___x_1094_);
return v___x_1140_;
}
}
else
{
lean_dec(v_tail_1110_);
lean_dec(v_head_1109_);
lean_dec(v___x_1094_);
return v___x_1139_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_tail_1110_);
lean_dec(v_head_1109_);
lean_dec(v___x_1094_);
v_a_1144_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1112_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1112_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_st_ref_get(v_a_1153_);
v___x_1165_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_toGoalState_1166_; lean_object* v_ematch_1167_; lean_object* v_a_1168_; lean_object* v_gmt_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_toGoalState_1166_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_toGoalState_1166_);
lean_dec(v___x_1164_);
v_ematch_1167_ = lean_ctor_get(v_toGoalState_1166_, 13);
lean_inc_ref(v_ematch_1167_);
lean_dec_ref(v_toGoalState_1166_);
v_a_1168_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1168_);
lean_dec_ref(v___x_1165_);
v_gmt_1169_ = lean_ctor_get(v_ematch_1167_, 1);
lean_inc(v_gmt_1169_);
lean_dec_ref(v_ematch_1167_);
v___x_1170_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1168_);
lean_dec(v_a_1168_);
v___x_1171_ = lean_box(0);
v___x_1172_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1169_, v___x_1170_, v___x_1171_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1172_, 0);
lean_dec(v_unused_1180_);
v___x_1174_ = v___x_1172_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_dec(v___x_1172_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1171_);
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1171_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
return v___x_1172_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___x_1164_);
v_a_1181_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1165_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1165_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_root_1189_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1202_, lean_object* v_as_x27_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1202_, v_as_x27_1203_, v_b_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1217_, lean_object* v_as_1218_, lean_object* v_as_x27_1219_, lean_object* v_b_1220_, lean_object* v_a_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1217_, v_as_x27_1219_, v_b_1220_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1234_, lean_object* v_as_1235_, lean_object* v_as_x27_1236_, lean_object* v_b_1237_, lean_object* v_a_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1234_, v_as_1235_, v_as_x27_1236_, v_b_1237_, v_a_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v_as_1235_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
if (lean_obj_tag(v_a_1251_) == 0)
{
lean_object* v___x_1253_; 
v___x_1253_ = l_List_reverse___redArg(v_a_1252_);
return v___x_1253_;
}
else
{
lean_object* v_head_1254_; lean_object* v_tail_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_head_1254_ = lean_ctor_get(v_a_1251_, 0);
v_tail_1255_ = lean_ctor_get(v_a_1251_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_a_1251_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v_a_1251_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_tail_1255_);
lean_inc(v_head_1254_);
lean_dec(v_a_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_MessageData_ofExpr(v_head_1254_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_a_1252_);
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_a_1252_);
v___x_1261_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v_a_1251_ = v_tail_1255_;
v_a_1252_ = v___x_1261_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_lams_1275_, lean_object* v_b_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1289_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1288_, v___y_1285_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1398_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1398_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1398_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1397_; 
v_fst_1294_ = lean_ctor_get(v_b_1276_, 0);
v_snd_1295_ = lean_ctor_get(v_b_1276_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_b_1276_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1297_ = v_b_1276_;
v_isShared_1298_ = v_isSharedCheck_1397_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_b_1276_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1397_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___x_1375_; 
v___x_1375_ = lean_unbox(v_a_1290_);
lean_dec(v_a_1290_);
if (v___x_1375_ == 0)
{
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc(v___y_1277_);
v___y_1344_ = v___y_1277_;
v___y_1345_ = v___y_1278_;
v___y_1346_ = v___y_1279_;
v___y_1347_ = v___y_1280_;
v___y_1348_ = v___y_1281_;
v___y_1349_ = v___y_1282_;
v___y_1350_ = v___y_1283_;
v___y_1351_ = v___y_1284_;
v___y_1352_ = v___y_1285_;
v___y_1353_ = v___y_1286_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_Grind_updateLastTag(v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v___x_1376_);
v___x_1377_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3);
lean_inc(v_snd_1295_);
v___x_1378_ = l_Lean_MessageData_ofExpr(v_snd_1295_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_1288_, v___x_1379_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec_ref(v___x_1380_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc(v___y_1277_);
v___y_1344_ = v___y_1277_;
v___y_1345_ = v___y_1278_;
v___y_1346_ = v___y_1279_;
v___y_1347_ = v___y_1280_;
v___y_1348_ = v___y_1281_;
v___y_1349_ = v___y_1282_;
v___y_1350_ = v___y_1283_;
v___y_1351_ = v___y_1284_;
v___y_1352_ = v___y_1285_;
v___y_1353_ = v___y_1286_;
goto v___jp_1343_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_del_object(v___x_1297_);
lean_dec(v_snd_1295_);
lean_dec(v_fst_1294_);
lean_del_object(v___x_1292_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_del_object(v___x_1297_);
lean_dec(v_snd_1295_);
lean_dec(v_fst_1294_);
lean_del_object(v___x_1292_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1389_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1376_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1376_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
v___jp_1299_:
{
if (lean_obj_tag(v_snd_1295_) == 5)
{
lean_object* v_fn_1310_; lean_object* v_arg_1311_; lean_object* v___x_1312_; 
lean_del_object(v___x_1292_);
v_fn_1310_ = lean_ctor_get(v_snd_1295_, 0);
lean_inc_ref(v_fn_1310_);
v_arg_1311_ = lean_ctor_get(v_snd_1295_, 1);
lean_inc_ref(v_arg_1311_);
v___x_1312_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1273_, v___y_1300_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_grind_internalize(v_snd_1295_, v_a_1313_, v___x_1314_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v___x_1315_);
v___x_1316_ = lean_array_push(v_fst_1294_, v_arg_1311_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v_fn_1310_);
lean_ctor_set(v___x_1297_, 0, v___x_1316_);
v___x_1318_ = v___x_1297_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_fn_1310_);
v___x_1318_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v_b_1276_ = v___x_1318_;
goto _start;
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_arg_1311_);
lean_dec_ref(v_fn_1310_);
lean_del_object(v___x_1297_);
lean_dec(v_fst_1294_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1321_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1315_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1315_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
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
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_arg_1311_);
lean_dec_ref(v_fn_1310_);
lean_dec_ref(v_snd_1295_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
lean_del_object(v___x_1297_);
lean_dec(v_fst_1294_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1329_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1312_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1312_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v___x_1338_; 
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
if (v_isShared_1298_ == 0)
{
v___x_1338_ = v___x_1297_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_fst_1294_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_snd_1295_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1338_);
v___x_1340_ = v___x_1292_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
v___jp_1343_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1295_, v_a_1274_, v___y_1344_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; uint8_t v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1356_ == 0)
{
v___y_1300_ = v___y_1344_;
v___y_1301_ = v___y_1345_;
v___y_1302_ = v___y_1346_;
v___y_1303_ = v___y_1347_;
v___y_1304_ = v___y_1348_;
v___y_1305_ = v___y_1349_;
v___y_1306_ = v___y_1350_;
v___y_1307_ = v___y_1351_;
v___y_1308_ = v___y_1352_;
v___y_1309_ = v___y_1353_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_inc(v_fst_1294_);
v___x_1357_ = l_Array_reverse___redArg(v_fst_1294_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc(v_snd_1295_);
v___x_1358_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1275_, v_snd_1295_, v___x_1357_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref(v___x_1358_);
v___y_1300_ = v___y_1344_;
v___y_1301_ = v___y_1345_;
v___y_1302_ = v___y_1346_;
v___y_1303_ = v___y_1347_;
v___y_1304_ = v___y_1348_;
v___y_1305_ = v___y_1349_;
v___y_1306_ = v___y_1350_;
v___y_1307_ = v___y_1351_;
v___y_1308_ = v___y_1352_;
v___y_1309_ = v___y_1353_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec(v___y_1344_);
lean_del_object(v___x_1297_);
lean_dec(v_snd_1295_);
lean_dec(v_fst_1294_);
lean_del_object(v___x_1292_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec(v___y_1344_);
lean_del_object(v___x_1297_);
lean_dec(v_snd_1295_);
lean_dec(v_fst_1294_);
lean_del_object(v___x_1292_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
v_a_1367_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1354_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1354_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
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
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v_b_1276_);
v_a_1399_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1289_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1289_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_lams_1409_, lean_object* v_b_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1407_, v_a_1408_, v_lams_1409_, v_b_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec_ref(v_lams_1409_);
lean_dec_ref(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1422_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__1));
v___x_1427_ = l_Lean_stringToMessageData(v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1428_, lean_object* v_lams_1429_, lean_object* v_as_x27_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
if (lean_obj_tag(v_as_x27_1430_) == 0)
{
lean_object* v___x_1443_; 
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_b_1431_);
return v___x_1443_;
}
else
{
lean_object* v_head_1444_; lean_object* v_tail_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1484_; 
v_head_1444_ = lean_ctor_get(v_as_x27_1430_, 0);
v_tail_1445_ = lean_ctor_get(v_as_x27_1430_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_as_x27_1430_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1447_ = v_as_x27_1430_;
v_isShared_1448_ = v_isSharedCheck_1484_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_tail_1445_);
lean_inc(v_head_1444_);
lean_dec(v_as_x27_1430_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1484_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; uint8_t v___x_1478_; 
v___x_1449_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1450_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1449_, v___y_1440_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = lean_box(0);
v___x_1453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
v___x_1478_ = lean_unbox(v_a_1451_);
lean_dec(v_a_1451_);
if (v___x_1478_ == 0)
{
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc(v___y_1432_);
v___y_1455_ = v___y_1432_;
v___y_1456_ = v___y_1433_;
v___y_1457_ = v___y_1434_;
v___y_1458_ = v___y_1435_;
v___y_1459_ = v___y_1436_;
v___y_1460_ = v___y_1437_;
v___y_1461_ = v___y_1438_;
v___y_1462_ = v___y_1439_;
v___y_1463_ = v___y_1440_;
v___y_1464_ = v___y_1441_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_Grind_updateLastTag(v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v___x_1479_);
v___x_1480_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__2);
lean_inc(v_head_1444_);
v___x_1481_ = l_Lean_MessageData_ofExpr(v_head_1444_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_1449_, v___x_1482_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref(v___x_1483_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc(v___y_1432_);
v___y_1455_ = v___y_1432_;
v___y_1456_ = v___y_1433_;
v___y_1457_ = v___y_1434_;
v___y_1458_ = v___y_1435_;
v___y_1459_ = v___y_1436_;
v___y_1460_ = v___y_1437_;
v___y_1461_ = v___y_1438_;
v___y_1462_ = v___y_1439_;
v___y_1463_ = v___y_1440_;
v___y_1464_ = v___y_1441_;
goto v___jp_1454_;
}
else
{
lean_del_object(v___x_1447_);
lean_dec(v_tail_1445_);
lean_dec(v_head_1444_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
return v___x_1483_;
}
}
else
{
lean_del_object(v___x_1447_);
lean_dec(v_tail_1445_);
lean_dec(v_head_1444_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
return v___x_1479_;
}
}
v___jp_1454_:
{
lean_object* v___x_1466_; 
lean_inc(v_head_1444_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 0);
lean_ctor_set(v___x_1447_, 1, v_head_1444_);
lean_ctor_set(v___x_1447_, 0, v___x_1453_);
v___x_1466_ = v___x_1447_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_head_1444_);
v___x_1466_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1444_, v_a_1428_, v_lams_1429_, v___x_1466_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v_head_1444_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref(v___x_1467_);
v_as_x27_1430_ = v_tail_1445_;
v_b_1431_ = v___x_1452_;
goto _start;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_tail_1445_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec(v___y_1432_);
v_a_1469_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1485_, lean_object* v_lams_1486_, lean_object* v_as_x27_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1485_, v_lams_1486_, v_as_x27_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec_ref(v_lams_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1500_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1507_, lean_object* v_lams_1508_, lean_object* v_as_1509_, size_t v_sz_1510_, size_t v_i_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_lt(v_i_1511_, v_sz_1510_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; 
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_b_1512_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1527_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1526_, v___y_1521_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; uint8_t v___x_1557_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = lean_box(0);
v_a_1530_ = lean_array_uget_borrowed(v_as_1509_, v_i_1511_);
v___x_1557_ = lean_unbox(v_a_1528_);
lean_dec(v_a_1528_);
if (v___x_1557_ == 0)
{
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc(v___y_1513_);
v___y_1532_ = v___y_1513_;
v___y_1533_ = v___y_1514_;
v___y_1534_ = v___y_1515_;
v___y_1535_ = v___y_1516_;
v___y_1536_ = v___y_1517_;
v___y_1537_ = v___y_1518_;
v___y_1538_ = v___y_1519_;
v___y_1539_ = v___y_1520_;
v___y_1540_ = v___y_1521_;
v___y_1541_ = v___y_1522_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Meta_Grind_updateLastTag(v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref(v___x_1558_);
v___x_1559_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1530_, v___y_1513_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__1);
lean_inc(v_a_1530_);
v___x_1562_ = l_Lean_MessageData_ofExpr(v_a_1530_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___closed__3);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1560_);
lean_dec(v_a_1560_);
v___x_1567_ = lean_box(0);
v___x_1568_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1566_, v___x_1567_);
v___x_1569_ = l_Lean_MessageData_ofList(v___x_1568_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1565_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_1526_, v___x_1570_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v___x_1571_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc(v___y_1513_);
v___y_1532_ = v___y_1513_;
v___y_1533_ = v___y_1514_;
v___y_1534_ = v___y_1515_;
v___y_1535_ = v___y_1516_;
v___y_1536_ = v___y_1517_;
v___y_1537_ = v___y_1518_;
v___y_1538_ = v___y_1519_;
v___y_1539_ = v___y_1520_;
v___y_1540_ = v___y_1521_;
v___y_1541_ = v___y_1522_;
goto v___jp_1531_;
}
else
{
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v___x_1571_;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
v_a_1572_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1559_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1559_);
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
else
{
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v___x_1558_;
}
}
v___jp_1531_:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1530_, v___y_1532_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1543_);
lean_dec(v_a_1543_);
v___x_1545_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1507_, v_lams_1508_, v___x_1544_, v___x_1529_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1545_) == 0)
{
size_t v___x_1546_; size_t v___x_1547_; 
lean_dec_ref(v___x_1545_);
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1511_, v___x_1546_);
v_i_1511_ = v___x_1547_;
v_b_1512_ = v___x_1529_;
goto _start;
}
else
{
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v___x_1545_;
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
v_a_1549_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1542_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1542_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
v_a_1580_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1527_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1527_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1588_ = _args[0];
lean_object* v_lams_1589_ = _args[1];
lean_object* v_as_1590_ = _args[2];
lean_object* v_sz_1591_ = _args[3];
lean_object* v_i_1592_ = _args[4];
lean_object* v_b_1593_ = _args[5];
lean_object* v___y_1594_ = _args[6];
lean_object* v___y_1595_ = _args[7];
lean_object* v___y_1596_ = _args[8];
lean_object* v___y_1597_ = _args[9];
lean_object* v___y_1598_ = _args[10];
lean_object* v___y_1599_ = _args[11];
lean_object* v___y_1600_ = _args[12];
lean_object* v___y_1601_ = _args[13];
lean_object* v___y_1602_ = _args[14];
lean_object* v___y_1603_ = _args[15];
lean_object* v___y_1604_ = _args[16];
_start:
{
size_t v_sz_boxed_1605_; size_t v_i_boxed_1606_; lean_object* v_res_1607_; 
v_sz_boxed_1605_ = lean_unbox_usize(v_sz_1591_);
lean_dec(v_sz_1591_);
v_i_boxed_1606_ = lean_unbox_usize(v_i_1592_);
lean_dec(v_i_1592_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1588_, v_lams_1589_, v_as_1590_, v_sz_boxed_1605_, v_i_boxed_1606_, v_b_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec_ref(v_as_1590_);
lean_dec_ref(v_lams_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1614_, lean_object* v_fns_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1627_ = lean_array_get_size(v_lams_1614_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_nat_dec_eq(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1630_ = lean_st_ref_get(v_a_1616_);
v___x_1631_ = l_Lean_instInhabitedExpr;
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_nat_sub(v___x_1627_, v___x_1632_);
v___x_1634_ = lean_array_get_borrowed(v___x_1631_, v_lams_1614_, v___x_1633_);
lean_dec(v___x_1633_);
lean_inc(v___x_1634_);
v___x_1635_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1630_, v___x_1634_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; uint8_t v___x_1663_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1635_);
v___x_1660_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1661_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1660_, v_a_1624_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = lean_unbox(v_a_1662_);
lean_dec(v_a_1662_);
if (v___x_1663_ == 0)
{
v___y_1638_ = v_a_1616_;
v___y_1639_ = v_a_1617_;
v___y_1640_ = v_a_1618_;
v___y_1641_ = v_a_1619_;
v___y_1642_ = v_a_1620_;
v___y_1643_ = v_a_1621_;
v___y_1644_ = v_a_1622_;
v___y_1645_ = v_a_1623_;
v___y_1646_ = v_a_1624_;
v___y_1647_ = v_a_1625_;
goto v___jp_1637_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Meta_Grind_updateLastTag(v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v___x_1664_);
v___x_1665_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1615_);
v___x_1666_ = lean_array_to_list(v_fns_1615_);
v___x_1667_ = lean_box(0);
v___x_1668_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1666_, v___x_1667_);
v___x_1669_ = l_Lean_MessageData_ofList(v___x_1668_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1665_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
lean_inc_ref(v_lams_1614_);
v___x_1673_ = lean_array_to_list(v_lams_1614_);
v___x_1674_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1673_, v___x_1667_);
v___x_1675_ = l_Lean_MessageData_ofList(v___x_1674_);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1672_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_1660_, v___x_1676_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_dec_ref(v___x_1677_);
v___y_1638_ = v_a_1616_;
v___y_1639_ = v_a_1617_;
v___y_1640_ = v_a_1618_;
v___y_1641_ = v_a_1619_;
v___y_1642_ = v_a_1620_;
v___y_1643_ = v_a_1621_;
v___y_1644_ = v_a_1622_;
v___y_1645_ = v_a_1623_;
v___y_1646_ = v_a_1624_;
v___y_1647_ = v_a_1625_;
goto v___jp_1637_;
}
else
{
lean_dec(v_a_1636_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_fns_1615_);
lean_dec_ref(v_lams_1614_);
return v___x_1677_;
}
}
else
{
lean_dec(v_a_1636_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_fns_1615_);
lean_dec_ref(v_lams_1614_);
return v___x_1664_;
}
}
v___jp_1637_:
{
lean_object* v___x_1648_; size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1648_ = lean_box(0);
v_sz_1649_ = lean_array_size(v_fns_1615_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1636_, v_lams_1614_, v_fns_1615_, v_sz_1649_, v___x_1650_, v___x_1648_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec_ref(v_fns_1615_);
lean_dec_ref(v_lams_1614_);
lean_dec(v_a_1636_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1651_, 0);
lean_dec(v_unused_1659_);
v___x_1653_ = v___x_1651_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v___x_1651_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1648_);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1648_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
return v___x_1651_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_fns_1615_);
lean_dec_ref(v_lams_1614_);
v_a_1678_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1635_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1635_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_fns_1615_);
lean_dec_ref(v_lams_1614_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1688_, lean_object* v_fns_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1688_, v_fns_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1702_, lean_object* v_lams_1703_, lean_object* v_as_1704_, lean_object* v_as_x27_1705_, lean_object* v_b_1706_, lean_object* v_a_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1702_, v_lams_1703_, v_as_x27_1705_, v_b_1706_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1720_ = _args[0];
lean_object* v_lams_1721_ = _args[1];
lean_object* v_as_1722_ = _args[2];
lean_object* v_as_x27_1723_ = _args[3];
lean_object* v_b_1724_ = _args[4];
lean_object* v_a_1725_ = _args[5];
lean_object* v___y_1726_ = _args[6];
lean_object* v___y_1727_ = _args[7];
lean_object* v___y_1728_ = _args[8];
lean_object* v___y_1729_ = _args[9];
lean_object* v___y_1730_ = _args[10];
lean_object* v___y_1731_ = _args[11];
lean_object* v___y_1732_ = _args[12];
lean_object* v___y_1733_ = _args[13];
lean_object* v___y_1734_ = _args[14];
lean_object* v___y_1735_ = _args[15];
lean_object* v___y_1736_ = _args[16];
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1720_, v_lams_1721_, v_as_1722_, v_as_x27_1723_, v_b_1724_, v_a_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v_as_1722_);
lean_dec_ref(v_lams_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1741_, lean_object* v_as_1742_, size_t v_sz_1743_, size_t v_i_1744_, lean_object* v_b_1745_){
_start:
{
lean_object* v_a_1747_; uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_lt(v_i_1744_, v_sz_1743_);
if (v___x_1751_ == 0)
{
return v_b_1745_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_a_1754_; 
lean_dec_ref(v_b_1745_);
v___x_1752_ = lean_box(0);
v___x_1753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1754_ = lean_array_uget_borrowed(v_as_1742_, v_i_1744_);
if (lean_obj_tag(v_a_1754_) == 6)
{
lean_object* v_binderType_1755_; uint8_t v___x_1756_; 
v_binderType_1755_ = lean_ctor_get(v_a_1754_, 1);
v___x_1756_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1741_, v_binderType_1755_);
if (v___x_1756_ == 0)
{
v_a_1747_ = v___x_1753_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_inc_ref(v_a_1754_);
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_a_1754_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1752_);
return v___x_1759_;
}
}
else
{
v_a_1747_ = v___x_1753_;
goto v___jp_1746_;
}
}
v___jp_1746_:
{
size_t v___x_1748_; size_t v___x_1749_; 
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1744_, v___x_1748_);
v_i_1744_ = v___x_1749_;
v_b_1745_ = v_a_1747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1760_, lean_object* v_as_1761_, lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_b_1764_){
_start:
{
size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1760_, v_as_1761_, v_sz_boxed_1765_, v_i_boxed_1766_, v_b_1764_);
lean_dec_ref(v_as_1761_);
lean_dec_ref(v_d_1760_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_1768_, lean_object* v_d_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; size_t v_sz_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v_fst_1775_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_1772_ = lean_array_size(v_lams_1768_);
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1769_, v_lams_1768_, v_sz_1772_, v___x_1773_, v___x_1771_);
v_fst_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_fst_1775_);
lean_dec_ref(v___x_1774_);
if (lean_obj_tag(v_fst_1775_) == 0)
{
return v___x_1770_;
}
else
{
lean_object* v_val_1776_; 
v_val_1776_ = lean_ctor_get(v_fst_1775_, 0);
lean_inc(v_val_1776_);
lean_dec_ref(v_fst_1775_);
return v_val_1776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_1777_, lean_object* v_d_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_1777_, v_d_1778_);
lean_dec_ref(v_d_1778_);
lean_dec_ref(v_lams_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_1790_, lean_object* v_lams_u2081_1791_, lean_object* v_as_1792_, size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_a_1808_; uint8_t v___x_1812_; 
v___x_1812_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_b_1795_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v_a_1815_; 
v___x_1814_ = lean_box(0);
v_a_1815_ = lean_array_uget_borrowed(v_as_1792_, v_i_1794_);
if (lean_obj_tag(v_a_1815_) == 6)
{
lean_object* v_binderType_1816_; lean_object* v_body_1817_; lean_object* v___x_1818_; 
v_binderType_1816_ = lean_ctor_get(v_a_1815_, 1);
v_body_1817_ = lean_ctor_get(v_a_1815_, 2);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc_ref(v_binderType_1816_);
v___x_1818_ = l_Lean_Meta_getLevel(v_binderType_1816_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_a_1819_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
lean_inc_ref(v___x_1822_);
v___x_1823_ = l_Lean_mkConst(v___x_1820_, v___x_1822_);
lean_inc_ref(v_binderType_1816_);
v___x_1824_ = l_Lean_Expr_app___override(v___x_1823_, v_binderType_1816_);
v___x_1825_ = lean_box(0);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
v___x_1826_ = l_Lean_Meta_synthInstance_x3f(v___x_1824_, v___x_1825_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
if (lean_obj_tag(v_a_1827_) == 1)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; uint8_t v___x_1894_; 
v_val_1828_ = lean_ctor_get(v_a_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref(v_a_1827_);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1894_ = l_Lean_Expr_hasLooseBVars(v_body_1817_);
if (v___x_1894_ == 0)
{
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc(v___y_1801_);
lean_inc_ref(v___y_1800_);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___y_1797_);
lean_inc(v___y_1796_);
v___y_1831_ = v___y_1796_;
v___y_1832_ = v___y_1797_;
v___y_1833_ = v___y_1798_;
v___y_1834_ = v___y_1799_;
v___y_1835_ = v___y_1800_;
v___y_1836_ = v___y_1801_;
v___y_1837_ = v___y_1802_;
v___y_1838_ = v___y_1803_;
v___y_1839_ = v___y_1804_;
v___y_1840_ = v___y_1805_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_1822_);
v___x_1896_ = l_Lean_mkConst(v___x_1895_, v___x_1822_);
lean_inc_ref(v_binderType_1816_);
v___x_1897_ = l_Lean_Expr_app___override(v___x_1896_, v_binderType_1816_);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
v___x_1898_ = l_Lean_Meta_synthInstance_x3f(v___x_1897_, v___x_1825_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
if (lean_obj_tag(v_a_1899_) == 0)
{
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1822_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
else
{
lean_dec_ref(v_a_1899_);
if (v___x_1894_ == 0)
{
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1822_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
else
{
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc(v___y_1801_);
lean_inc_ref(v___y_1800_);
lean_inc(v___y_1799_);
lean_inc_ref(v___y_1798_);
lean_inc(v___y_1797_);
lean_inc(v___y_1796_);
v___y_1831_ = v___y_1796_;
v___y_1832_ = v___y_1797_;
v___y_1833_ = v___y_1798_;
v___y_1834_ = v___y_1799_;
v___y_1835_ = v___y_1800_;
v___y_1836_ = v___y_1801_;
v___y_1837_ = v___y_1802_;
v___y_1838_ = v___y_1803_;
v___y_1839_ = v___y_1804_;
v___y_1840_ = v___y_1805_;
goto v___jp_1830_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1822_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1900_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
v___jp_1830_:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_1790_, v_binderType_1816_);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v_val_1842_; 
v_val_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1842_);
lean_dec_ref(v___x_1841_);
if (lean_obj_tag(v_val_1842_) == 6)
{
lean_object* v_binderType_1843_; lean_object* v_body_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_binderType_1843_ = lean_ctor_get(v_val_1842_, 1);
lean_inc_ref(v_binderType_1843_);
v_body_1844_ = lean_ctor_get(v_val_1842_, 2);
lean_inc_ref(v_body_1844_);
lean_dec_ref(v_val_1842_);
v___x_1845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_1846_ = l_Lean_mkConst(v___x_1845_, v___x_1822_);
v___x_1847_ = l_Lean_mkAppB(v___x_1846_, v_binderType_1843_, v_val_1828_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v___y_1831_);
v___x_1848_ = l_Lean_Meta_Grind_preprocessLight(v___x_1847_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_array_fget_borrowed(v_lams_u2081_1791_, v___x_1829_);
v___x_1851_ = lean_array_fget_borrowed(v_lams_u2082_1790_, v___x_1829_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc(v___x_1851_);
lean_inc(v___x_1850_);
v___x_1852_ = lean_grind_mk_eq_proof(v___x_1850_, v___x_1851_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = lean_expr_instantiate1(v_body_1817_, v_a_1849_);
v___x_1855_ = lean_expr_instantiate1(v_body_1844_, v_a_1849_);
lean_dec_ref(v_body_1844_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
v___x_1856_ = l_Lean_Meta_mkCongrFun(v_a_1853_, v_a_1849_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
v___x_1858_ = l_Lean_Meta_mkEq(v___x_1854_, v___x_1855_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_Meta_mkExpectedPropHint(v_a_1857_, v_a_1859_);
v___x_1861_ = l_Lean_Meta_Grind_pushNewFact(v___x_1860_, v___x_1829_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref(v___x_1861_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
else
{
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
return v___x_1861_;
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1857_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1862_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1858_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1858_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v___x_1855_);
lean_dec_ref(v___x_1854_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1870_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1856_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1856_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1849_);
lean_dec_ref(v_body_1844_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1878_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1852_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1852_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v_body_1844_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1886_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1848_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1848_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_dec(v_val_1842_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1822_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
}
else
{
lean_dec(v___x_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v_val_1828_);
lean_dec_ref(v___x_1822_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
}
}
else
{
lean_dec(v_a_1827_);
lean_dec_ref(v___x_1822_);
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___x_1822_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1908_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1826_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1826_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
v_a_1916_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1818_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1818_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
v_a_1808_ = v___x_1814_;
goto v___jp_1807_;
}
}
v___jp_1807_:
{
size_t v___x_1809_; size_t v___x_1810_; 
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_add(v_i_1794_, v___x_1809_);
v_i_1794_ = v___x_1810_;
v_b_1795_ = v_a_1808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_1924_ = _args[0];
lean_object* v_lams_u2081_1925_ = _args[1];
lean_object* v_as_1926_ = _args[2];
lean_object* v_sz_1927_ = _args[3];
lean_object* v_i_1928_ = _args[4];
lean_object* v_b_1929_ = _args[5];
lean_object* v___y_1930_ = _args[6];
lean_object* v___y_1931_ = _args[7];
lean_object* v___y_1932_ = _args[8];
lean_object* v___y_1933_ = _args[9];
lean_object* v___y_1934_ = _args[10];
lean_object* v___y_1935_ = _args[11];
lean_object* v___y_1936_ = _args[12];
lean_object* v___y_1937_ = _args[13];
lean_object* v___y_1938_ = _args[14];
lean_object* v___y_1939_ = _args[15];
lean_object* v___y_1940_ = _args[16];
_start:
{
size_t v_sz_boxed_1941_; size_t v_i_boxed_1942_; lean_object* v_res_1943_; 
v_sz_boxed_1941_ = lean_unbox_usize(v_sz_1927_);
lean_dec(v_sz_1927_);
v_i_boxed_1942_ = lean_unbox_usize(v_i_1928_);
lean_dec(v_i_1928_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_1924_, v_lams_u2081_1925_, v_as_1926_, v_sz_boxed_1941_, v_i_boxed_1942_, v_b_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec_ref(v_as_1926_);
lean_dec_ref(v_lams_u2081_1925_);
lean_dec_ref(v_lams_u2082_1924_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_1944_, lean_object* v_lams_u2082_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = lean_array_get_size(v_lams_u2081_1944_);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_nat_dec_eq(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1960_ = lean_array_get_size(v_lams_u2082_1945_);
v___x_1961_ = lean_nat_dec_eq(v___x_1960_, v___x_1958_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; size_t v_sz_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1962_ = lean_box(0);
v_sz_1963_ = lean_array_size(v_lams_u2081_1944_);
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_1945_, v_lams_u2081_1944_, v_lams_u2081_1944_, v_sz_1963_, v___x_1964_, v___x_1962_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1965_, 0);
lean_dec(v_unused_1973_);
v___x_1967_ = v___x_1965_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v___x_1965_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1962_);
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1962_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
return v___x_1965_;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec(v_a_1946_);
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec(v_a_1946_);
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_1978_, lean_object* v_lams_u2082_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_1978_, v_lams_u2082_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec_ref(v_lams_u2082_1979_);
lean_dec_ref(v_lams_u2081_1978_);
return v_res_1991_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_1992_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_1994_){
_start:
{
uint8_t v_res_1995_; lean_object* v_r_1996_; 
v_res_1995_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_1994_);
lean_dec_ref(v_x_1994_);
v_r_1996_ = lean_box(v_res_1995_);
return v_r_1996_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_1997_, lean_object* v_x_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2000_, lean_object* v_x_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2000_, v_x_2001_);
lean_dec_ref(v_x_2001_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2004_, lean_object* v_v_2005_, lean_object* v_i_2006_){
_start:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = lean_array_get_size(v_xs_2004_);
v___x_2008_ = lean_nat_dec_lt(v_i_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_i_2006_);
v___x_2009_ = lean_box(0);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = lean_array_fget_borrowed(v_xs_2004_, v_i_2006_);
v___x_2011_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2010_, v_v_2005_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_i_2006_, v___x_2012_);
lean_dec(v_i_2006_);
v_i_2006_ = v___x_2013_;
goto _start;
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_i_2006_);
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2016_, lean_object* v_v_2017_, lean_object* v_i_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2016_, v_v_2017_, v_i_2018_);
lean_dec_ref(v_v_2017_);
lean_dec_ref(v_xs_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2020_, lean_object* v_v_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2023_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2020_, v_v_2021_, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2024_, lean_object* v_v_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2024_, v_v_2025_);
lean_dec_ref(v_v_2025_);
lean_dec_ref(v_xs_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2027_, size_t v_x_2028_, lean_object* v_x_2029_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v_es_2030_; lean_object* v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v_j_2035_; lean_object* v_entry_2036_; 
v_es_2030_ = lean_ctor_get(v_x_2027_, 0);
v___x_2031_ = lean_box(2);
v___x_2032_ = ((size_t)5ULL);
v___x_2033_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2034_ = lean_usize_land(v_x_2028_, v___x_2033_);
v_j_2035_ = lean_usize_to_nat(v___x_2034_);
v_entry_2036_ = lean_array_get(v___x_2031_, v_es_2030_, v_j_2035_);
switch(lean_obj_tag(v_entry_2036_))
{
case 0:
{
lean_object* v_key_2037_; uint8_t v___x_2038_; 
v_key_2037_ = lean_ctor_get(v_entry_2036_, 0);
lean_inc(v_key_2037_);
lean_dec_ref(v_entry_2036_);
v___x_2038_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2029_, v_key_2037_);
lean_dec(v_key_2037_);
if (v___x_2038_ == 0)
{
lean_dec(v_j_2035_);
return v_x_2027_;
}
else
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
lean_inc_ref(v_es_2030_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_x_2027_, 0);
lean_dec(v_unused_2047_);
v___x_2040_ = v_x_2027_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_x_2027_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_array_set(v_es_2030_, v_j_2035_, v___x_2031_);
lean_dec(v_j_2035_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
case 1:
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2081_; 
lean_inc_ref(v_es_2030_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v_x_2027_, 0);
lean_dec(v_unused_2082_);
v___x_2049_ = v_x_2027_;
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v_x_2027_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_node_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2080_; 
v_node_2051_ = lean_ctor_get(v_entry_2036_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_entry_2036_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2053_ = v_entry_2036_;
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_node_2051_);
lean_dec(v_entry_2036_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_entries_2055_; size_t v___x_2056_; lean_object* v_newNode_2057_; lean_object* v___x_2058_; 
v_entries_2055_ = lean_array_set(v_es_2030_, v_j_2035_, v___x_2031_);
v___x_2056_ = lean_usize_shift_right(v_x_2028_, v___x_2032_);
v_newNode_2057_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2051_, v___x_2056_, v_x_2029_);
lean_inc_ref(v_newNode_2057_);
v___x_2058_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2057_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v___x_2060_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v_newNode_2057_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_newNode_2057_);
v___x_2060_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_array_set(v_entries_2055_, v_j_2035_, v___x_2060_);
lean_dec(v_j_2035_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2061_);
v___x_2063_ = v___x_2049_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_val_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_newNode_2057_);
lean_del_object(v___x_2053_);
v_val_2066_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2066_);
lean_dec_ref(v___x_2058_);
v_fst_2067_ = lean_ctor_get(v_val_2066_, 0);
v_snd_2068_ = lean_ctor_get(v_val_2066_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_val_2066_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2070_ = v_val_2066_;
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_val_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_fst_2067_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_snd_2068_);
v___x_2073_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = lean_array_set(v_entries_2055_, v_j_2035_, v___x_2073_);
lean_dec(v_j_2035_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2074_);
v___x_2076_ = v___x_2049_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
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
}
}
default: 
{
lean_dec(v_j_2035_);
return v_x_2027_;
}
}
}
else
{
lean_object* v_ks_2083_; lean_object* v_vs_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2098_; 
v_ks_2083_ = lean_ctor_get(v_x_2027_, 0);
v_vs_2084_ = lean_ctor_get(v_x_2027_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2086_ = v_x_2027_;
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_vs_2084_);
lean_inc(v_ks_2083_);
lean_dec(v_x_2027_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2098_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2083_, v_x_2029_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2090_; 
if (v_isShared_2087_ == 0)
{
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_ks_2083_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_vs_2084_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
else
{
lean_object* v_val_2092_; lean_object* v_keys_x27_2093_; lean_object* v_vals_x27_2094_; lean_object* v___x_2096_; 
v_val_2092_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2092_);
lean_dec_ref(v___x_2088_);
lean_inc(v_val_2092_);
v_keys_x27_2093_ = l_Array_eraseIdx___redArg(v_ks_2083_, v_val_2092_);
v_vals_x27_2094_ = l_Array_eraseIdx___redArg(v_vs_2084_, v_val_2092_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v_vals_x27_2094_);
lean_ctor_set(v___x_2086_, 0, v_keys_x27_2093_);
v___x_2096_ = v___x_2086_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_keys_x27_2093_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_vals_x27_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_){
_start:
{
size_t v_x_22650__boxed_2102_; lean_object* v_res_2103_; 
v_x_22650__boxed_2102_ = lean_unbox_usize(v_x_2100_);
lean_dec(v_x_2100_);
v_res_2103_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2099_, v_x_22650__boxed_2102_, v_x_2101_);
lean_dec_ref(v_x_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
uint64_t v___x_2106_; size_t v_h_2107_; lean_object* v___x_2108_; 
v___x_2106_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2105_);
v_h_2107_ = lean_uint64_to_usize(v___x_2106_);
v___x_2108_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2104_, v_h_2107_, v_x_2105_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2109_, v_x_2110_);
lean_dec_ref(v_x_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
if (lean_obj_tag(v_as_2112_) == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec(v___y_2113_);
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; lean_object* v___x_2128_; 
v_head_2126_ = lean_ctor_get(v_as_2112_, 0);
lean_inc(v_head_2126_);
v_tail_2127_ = lean_ctor_get(v_as_2112_, 1);
lean_inc(v_tail_2127_);
lean_dec_ref(v_as_2112_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc(v___y_2113_);
v___x_2128_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2126_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_dec_ref(v___x_2128_);
v_as_2112_ = v_tail_2127_;
goto _start;
}
else
{
lean_dec(v_tail_2127_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec(v___y_2113_);
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2143_, lean_object* v_vals_2144_, lean_object* v_i_2145_, lean_object* v_k_2146_){
_start:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_array_get_size(v_keys_2143_);
v___x_2148_ = lean_nat_dec_lt(v_i_2145_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec(v_i_2145_);
v___x_2149_ = lean_box(0);
return v___x_2149_;
}
else
{
lean_object* v_k_x27_2150_; uint8_t v___x_2151_; 
v_k_x27_2150_ = lean_array_fget_borrowed(v_keys_2143_, v_i_2145_);
v___x_2151_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2146_, v_k_x27_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_add(v_i_2145_, v___x_2152_);
lean_dec(v_i_2145_);
v_i_2145_ = v___x_2153_;
goto _start;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_array_fget_borrowed(v_vals_2144_, v_i_2145_);
lean_dec(v_i_2145_);
lean_inc(v___x_2155_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2157_, lean_object* v_vals_2158_, lean_object* v_i_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2157_, v_vals_2158_, v_i_2159_, v_k_2160_);
lean_dec_ref(v_k_2160_);
lean_dec_ref(v_vals_2158_);
lean_dec_ref(v_keys_2157_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2162_, size_t v_x_2163_, lean_object* v_x_2164_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v_es_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2186_; 
v_es_2165_ = lean_ctor_get(v_x_2162_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_x_2162_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2167_ = v_x_2162_;
v_isShared_2168_ = v_isSharedCheck_2186_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_es_2165_);
lean_dec(v_x_2162_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2186_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; lean_object* v_j_2173_; lean_object* v___x_2174_; 
v___x_2169_ = lean_box(2);
v___x_2170_ = ((size_t)5ULL);
v___x_2171_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2172_ = lean_usize_land(v_x_2163_, v___x_2171_);
v_j_2173_ = lean_usize_to_nat(v___x_2172_);
v___x_2174_ = lean_array_get(v___x_2169_, v_es_2165_, v_j_2173_);
lean_dec(v_j_2173_);
lean_dec_ref(v_es_2165_);
switch(lean_obj_tag(v___x_2174_))
{
case 0:
{
lean_object* v_key_2175_; lean_object* v_val_2176_; uint8_t v___x_2177_; 
v_key_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_key_2175_);
v_val_2176_ = lean_ctor_get(v___x_2174_, 1);
lean_inc(v_val_2176_);
lean_dec_ref(v___x_2174_);
v___x_2177_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2164_, v_key_2175_);
lean_dec(v_key_2175_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_val_2176_);
lean_del_object(v___x_2167_);
v___x_2178_ = lean_box(0);
return v___x_2178_;
}
else
{
lean_object* v___x_2180_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 1);
lean_ctor_set(v___x_2167_, 0, v_val_2176_);
v___x_2180_ = v___x_2167_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_val_2176_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
case 1:
{
lean_object* v_node_2182_; size_t v___x_2183_; 
lean_del_object(v___x_2167_);
v_node_2182_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_node_2182_);
lean_dec_ref(v___x_2174_);
v___x_2183_ = lean_usize_shift_right(v_x_2163_, v___x_2170_);
v_x_2162_ = v_node_2182_;
v_x_2163_ = v___x_2183_;
goto _start;
}
default: 
{
lean_object* v___x_2185_; 
lean_del_object(v___x_2167_);
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_ks_2187_; lean_object* v_vs_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_ks_2187_ = lean_ctor_get(v_x_2162_, 0);
lean_inc_ref(v_ks_2187_);
v_vs_2188_ = lean_ctor_get(v_x_2162_, 1);
lean_inc_ref(v_vs_2188_);
lean_dec_ref(v_x_2162_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2187_, v_vs_2188_, v___x_2189_, v_x_2164_);
lean_dec_ref(v_vs_2188_);
lean_dec_ref(v_ks_2187_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
size_t v_x_22869__boxed_2194_; lean_object* v_res_2195_; 
v_x_22869__boxed_2194_ = lean_unbox_usize(v_x_2192_);
lean_dec(v_x_2192_);
v_res_2195_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2191_, v_x_22869__boxed_2194_, v_x_2193_);
lean_dec_ref(v_x_2193_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
uint64_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2197_);
v___x_2199_ = lean_uint64_to_usize(v___x_2198_);
v___x_2200_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2196_, v___x_2199_, v_x_2197_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2201_, v_x_2202_);
lean_dec_ref(v_x_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2204_, lean_object* v_b_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
if (lean_obj_tag(v_as_x27_2204_) == 0)
{
lean_object* v___x_2217_; 
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec(v___y_2206_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_b_2205_);
return v___x_2217_;
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; lean_object* v___x_2220_; lean_object* v_toGoalState_2221_; lean_object* v_ematch_2222_; lean_object* v_delayedThmInsts_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_head_2218_ = lean_ctor_get(v_as_x27_2204_, 0);
v_tail_2219_ = lean_ctor_get(v_as_x27_2204_, 1);
v___x_2220_ = lean_st_ref_get(v___y_2206_);
v_toGoalState_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_toGoalState_2221_);
lean_dec(v___x_2220_);
v_ematch_2222_ = lean_ctor_get(v_toGoalState_2221_, 13);
lean_inc_ref(v_ematch_2222_);
lean_dec_ref(v_toGoalState_2221_);
v_delayedThmInsts_2223_ = lean_ctor_get(v_ematch_2222_, 10);
lean_inc_ref(v_delayedThmInsts_2223_);
lean_dec_ref(v_ematch_2222_);
v___x_2224_ = lean_box(0);
v___x_2225_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2223_, v_head_2218_);
if (lean_obj_tag(v___x_2225_) == 1)
{
lean_object* v_val_2226_; lean_object* v___x_2227_; lean_object* v_toGoalState_2228_; lean_object* v_ematch_2229_; lean_object* v_mvarId_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2285_; 
v_val_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = lean_st_ref_take(v___y_2206_);
v_toGoalState_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc_ref(v_toGoalState_2228_);
v_ematch_2229_ = lean_ctor_get(v_toGoalState_2228_, 13);
lean_inc_ref(v_ematch_2229_);
v_mvarId_2230_ = lean_ctor_get(v___x_2227_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2227_, 0);
lean_dec(v_unused_2286_);
v___x_2232_ = v___x_2227_;
v_isShared_2233_ = v_isSharedCheck_2285_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_mvarId_2230_);
lean_dec(v___x_2227_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2285_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_nextDeclIdx_2234_; lean_object* v_canon_2235_; lean_object* v_enodeMap_2236_; lean_object* v_exprs_2237_; lean_object* v_parents_2238_; lean_object* v_congrTable_2239_; lean_object* v_appMap_2240_; lean_object* v_indicesFound_2241_; lean_object* v_newFacts_2242_; uint8_t v_inconsistent_2243_; lean_object* v_nextIdx_2244_; lean_object* v_newRawFacts_2245_; lean_object* v_facts_2246_; lean_object* v_extThms_2247_; lean_object* v_inj_2248_; lean_object* v_split_2249_; lean_object* v_clean_2250_; lean_object* v_sstates_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2283_; 
v_nextDeclIdx_2234_ = lean_ctor_get(v_toGoalState_2228_, 0);
v_canon_2235_ = lean_ctor_get(v_toGoalState_2228_, 1);
v_enodeMap_2236_ = lean_ctor_get(v_toGoalState_2228_, 2);
v_exprs_2237_ = lean_ctor_get(v_toGoalState_2228_, 3);
v_parents_2238_ = lean_ctor_get(v_toGoalState_2228_, 4);
v_congrTable_2239_ = lean_ctor_get(v_toGoalState_2228_, 5);
v_appMap_2240_ = lean_ctor_get(v_toGoalState_2228_, 6);
v_indicesFound_2241_ = lean_ctor_get(v_toGoalState_2228_, 7);
v_newFacts_2242_ = lean_ctor_get(v_toGoalState_2228_, 8);
v_inconsistent_2243_ = lean_ctor_get_uint8(v_toGoalState_2228_, sizeof(void*)*18);
v_nextIdx_2244_ = lean_ctor_get(v_toGoalState_2228_, 9);
v_newRawFacts_2245_ = lean_ctor_get(v_toGoalState_2228_, 10);
v_facts_2246_ = lean_ctor_get(v_toGoalState_2228_, 11);
v_extThms_2247_ = lean_ctor_get(v_toGoalState_2228_, 12);
v_inj_2248_ = lean_ctor_get(v_toGoalState_2228_, 14);
v_split_2249_ = lean_ctor_get(v_toGoalState_2228_, 15);
v_clean_2250_ = lean_ctor_get(v_toGoalState_2228_, 16);
v_sstates_2251_ = lean_ctor_get(v_toGoalState_2228_, 17);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_toGoalState_2228_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_toGoalState_2228_, 13);
lean_dec(v_unused_2284_);
v___x_2253_ = v_toGoalState_2228_;
v_isShared_2254_ = v_isSharedCheck_2283_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_sstates_2251_);
lean_inc(v_clean_2250_);
lean_inc(v_split_2249_);
lean_inc(v_inj_2248_);
lean_inc(v_extThms_2247_);
lean_inc(v_facts_2246_);
lean_inc(v_newRawFacts_2245_);
lean_inc(v_nextIdx_2244_);
lean_inc(v_newFacts_2242_);
lean_inc(v_indicesFound_2241_);
lean_inc(v_appMap_2240_);
lean_inc(v_congrTable_2239_);
lean_inc(v_parents_2238_);
lean_inc(v_exprs_2237_);
lean_inc(v_enodeMap_2236_);
lean_inc(v_canon_2235_);
lean_inc(v_nextDeclIdx_2234_);
lean_dec(v_toGoalState_2228_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2283_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v_thmMap_2255_; lean_object* v_gmt_2256_; lean_object* v_thms_2257_; lean_object* v_newThms_2258_; lean_object* v_numInstances_2259_; lean_object* v_numDelayedInstances_2260_; lean_object* v_num_2261_; lean_object* v_preInstances_2262_; lean_object* v_nextThmIdx_2263_; lean_object* v_matchEqNames_2264_; lean_object* v_delayedThmInsts_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2282_; 
v_thmMap_2255_ = lean_ctor_get(v_ematch_2229_, 0);
v_gmt_2256_ = lean_ctor_get(v_ematch_2229_, 1);
v_thms_2257_ = lean_ctor_get(v_ematch_2229_, 2);
v_newThms_2258_ = lean_ctor_get(v_ematch_2229_, 3);
v_numInstances_2259_ = lean_ctor_get(v_ematch_2229_, 4);
v_numDelayedInstances_2260_ = lean_ctor_get(v_ematch_2229_, 5);
v_num_2261_ = lean_ctor_get(v_ematch_2229_, 6);
v_preInstances_2262_ = lean_ctor_get(v_ematch_2229_, 7);
v_nextThmIdx_2263_ = lean_ctor_get(v_ematch_2229_, 8);
v_matchEqNames_2264_ = lean_ctor_get(v_ematch_2229_, 9);
v_delayedThmInsts_2265_ = lean_ctor_get(v_ematch_2229_, 10);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_ematch_2229_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2267_ = v_ematch_2229_;
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_delayedThmInsts_2265_);
lean_inc(v_matchEqNames_2264_);
lean_inc(v_nextThmIdx_2263_);
lean_inc(v_preInstances_2262_);
lean_inc(v_num_2261_);
lean_inc(v_numDelayedInstances_2260_);
lean_inc(v_numInstances_2259_);
lean_inc(v_newThms_2258_);
lean_inc(v_thms_2257_);
lean_inc(v_gmt_2256_);
lean_inc(v_thmMap_2255_);
lean_dec(v_ematch_2229_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2282_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2265_, v_head_2218_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 10, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_thmMap_2255_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_gmt_2256_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_thms_2257_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_newThms_2258_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_numInstances_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 5, v_numDelayedInstances_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 6, v_num_2261_);
lean_ctor_set(v_reuseFailAlloc_2281_, 7, v_preInstances_2262_);
lean_ctor_set(v_reuseFailAlloc_2281_, 8, v_nextThmIdx_2263_);
lean_ctor_set(v_reuseFailAlloc_2281_, 9, v_matchEqNames_2264_);
lean_ctor_set(v_reuseFailAlloc_2281_, 10, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 13, v___x_2271_);
v___x_2273_ = v___x_2253_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_nextDeclIdx_2234_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_canon_2235_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_enodeMap_2236_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_exprs_2237_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_parents_2238_);
lean_ctor_set(v_reuseFailAlloc_2280_, 5, v_congrTable_2239_);
lean_ctor_set(v_reuseFailAlloc_2280_, 6, v_appMap_2240_);
lean_ctor_set(v_reuseFailAlloc_2280_, 7, v_indicesFound_2241_);
lean_ctor_set(v_reuseFailAlloc_2280_, 8, v_newFacts_2242_);
lean_ctor_set(v_reuseFailAlloc_2280_, 9, v_nextIdx_2244_);
lean_ctor_set(v_reuseFailAlloc_2280_, 10, v_newRawFacts_2245_);
lean_ctor_set(v_reuseFailAlloc_2280_, 11, v_facts_2246_);
lean_ctor_set(v_reuseFailAlloc_2280_, 12, v_extThms_2247_);
lean_ctor_set(v_reuseFailAlloc_2280_, 13, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2280_, 14, v_inj_2248_);
lean_ctor_set(v_reuseFailAlloc_2280_, 15, v_split_2249_);
lean_ctor_set(v_reuseFailAlloc_2280_, 16, v_clean_2250_);
lean_ctor_set(v_reuseFailAlloc_2280_, 17, v_sstates_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*18, v_inconsistent_2243_);
v___x_2273_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2273_);
v___x_2275_ = v___x_2232_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_mvarId_2230_);
v___x_2275_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_st_ref_set(v___y_2206_, v___x_2275_);
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
lean_inc(v___y_2211_);
lean_inc_ref(v___y_2210_);
lean_inc(v___y_2209_);
lean_inc_ref(v___y_2208_);
lean_inc(v___y_2207_);
lean_inc(v___y_2206_);
v___x_2277_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2226_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref(v___x_2277_);
v_as_x27_2204_ = v_tail_2219_;
v_b_2205_ = v___x_2224_;
goto _start;
}
else
{
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec(v___y_2206_);
return v___x_2277_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2225_);
v_as_x27_2204_ = v_tail_2219_;
v_b_2205_ = v___x_2224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2288_, v_b_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v_as_x27_2288_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2303_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2343_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2343_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2343_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_unbox(v_a_2315_);
lean_dec(v_a_2315_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v_toGoalState_2321_; lean_object* v_ematch_2322_; lean_object* v_delayedThmInsts_2323_; uint8_t v___x_2324_; 
v___x_2320_ = lean_st_ref_get(v_a_2303_);
v_toGoalState_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc_ref(v_toGoalState_2321_);
lean_dec(v___x_2320_);
v_ematch_2322_ = lean_ctor_get(v_toGoalState_2321_, 13);
lean_inc_ref(v_ematch_2322_);
lean_dec_ref(v_toGoalState_2321_);
v_delayedThmInsts_2323_ = lean_ctor_get(v_ematch_2322_, 10);
lean_inc_ref(v_delayedThmInsts_2323_);
lean_dec_ref(v_ematch_2322_);
v___x_2324_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2323_);
lean_dec_ref(v_delayedThmInsts_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_del_object(v___x_2317_);
v___x_2325_ = lean_box(0);
v___x_2326_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2302_, v___x_2325_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v___x_2326_, 0);
lean_dec(v_unused_2334_);
v___x_2328_ = v___x_2326_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v___x_2326_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2325_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
return v___x_2326_;
}
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec(v_a_2303_);
v___x_2335_ = lean_box(0);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2335_);
v___x_2337_ = v___x_2317_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec(v_a_2303_);
v___x_2339_ = lean_box(0);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2339_);
v___x_2341_ = v___x_2317_;
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
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec(v_a_2303_);
v_a_2344_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2314_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2314_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_toPropagateDown_2352_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2366_, v_x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2369_, v_x_2370_, v_x_2371_);
lean_dec_ref(v_x_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2377_, v_x_2378_, v_x_2379_);
lean_dec_ref(v_x_2379_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2381_, lean_object* v_as_x27_2382_, lean_object* v_b_2383_, lean_object* v_a_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2382_, v_b_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2397_, lean_object* v_as_x27_2398_, lean_object* v_b_2399_, lean_object* v_a_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2397_, v_as_x27_2398_, v_b_2399_, v_a_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v_as_x27_2398_);
lean_dec(v_as_2397_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2413_, lean_object* v_x_2414_, size_t v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2414_, v_x_2415_, v_x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_, lean_object* v_x_2421_){
_start:
{
size_t v_x_23208__boxed_2422_; lean_object* v_res_2423_; 
v_x_23208__boxed_2422_ = lean_unbox_usize(v_x_2420_);
lean_dec(v_x_2420_);
v_res_2423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2418_, v_x_2419_, v_x_23208__boxed_2422_, v_x_2421_);
lean_dec_ref(v_x_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2424_, lean_object* v_x_2425_, size_t v_x_2426_, lean_object* v_x_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2425_, v_x_2426_, v_x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
size_t v_x_23219__boxed_2433_; lean_object* v_res_2434_; 
v_x_23219__boxed_2433_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_res_2434_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2429_, v_x_2430_, v_x_23219__boxed_2433_, v_x_2432_);
lean_dec_ref(v_x_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2435_, lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_heq_2438_, lean_object* v_i_2439_, lean_object* v_k_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2436_, v_vals_2437_, v_i_2439_, v_k_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2442_, lean_object* v_keys_2443_, lean_object* v_vals_2444_, lean_object* v_heq_2445_, lean_object* v_i_2446_, lean_object* v_k_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2442_, v_keys_2443_, v_vals_2444_, v_heq_2445_, v_i_2446_, v_k_2447_);
lean_dec_ref(v_k_2447_);
lean_dec_ref(v_vals_2444_);
lean_dec_ref(v_keys_2443_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2449_, lean_object* v_keys_2450_, lean_object* v_vals_2451_, lean_object* v_i_2452_, lean_object* v_k_2453_){
_start:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = lean_array_get_size(v_keys_2450_);
v___x_2455_ = lean_nat_dec_lt(v_i_2452_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v_k_2453_);
lean_dec(v_i_2452_);
lean_dec_ref(v___x_2449_);
v___x_2456_ = lean_box(0);
return v___x_2456_;
}
else
{
lean_object* v_k_x27_2457_; uint8_t v___x_2458_; 
v_k_x27_2457_ = lean_array_fget_borrowed(v_keys_2450_, v_i_2452_);
lean_inc(v_k_x27_2457_);
lean_inc_ref(v_k_2453_);
lean_inc_ref(v___x_2449_);
v___x_2458_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_2449_, v_k_2453_, v_k_x27_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_nat_add(v_i_2452_, v___x_2459_);
lean_dec(v_i_2452_);
v_i_2452_ = v___x_2460_;
goto _start;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec_ref(v_k_2453_);
lean_dec_ref(v___x_2449_);
v___x_2462_ = lean_array_fget_borrowed(v_vals_2451_, v_i_2452_);
lean_dec(v_i_2452_);
lean_inc(v___x_2462_);
lean_inc(v_k_x27_2457_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_k_x27_2457_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
return v___x_2464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2465_, lean_object* v_keys_2466_, lean_object* v_vals_2467_, lean_object* v_i_2468_, lean_object* v_k_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2465_, v_keys_2466_, v_vals_2467_, v_i_2468_, v_k_2469_);
lean_dec_ref(v_vals_2467_);
lean_dec_ref(v_keys_2466_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2471_, lean_object* v_x_2472_, size_t v_x_2473_, lean_object* v_x_2474_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
lean_object* v_es_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2503_; 
v_es_2475_ = lean_ctor_get(v_x_2472_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_x_2472_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2477_ = v_x_2472_;
v_isShared_2478_ = v_isSharedCheck_2503_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_es_2475_);
lean_dec(v_x_2472_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2503_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; size_t v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; lean_object* v_j_2483_; lean_object* v___x_2484_; 
v___x_2479_ = lean_box(2);
v___x_2480_ = ((size_t)5ULL);
v___x_2481_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2482_ = lean_usize_land(v_x_2473_, v___x_2481_);
v_j_2483_ = lean_usize_to_nat(v___x_2482_);
v___x_2484_ = lean_array_get(v___x_2479_, v_es_2475_, v_j_2483_);
lean_dec(v_j_2483_);
lean_dec_ref(v_es_2475_);
switch(lean_obj_tag(v___x_2484_))
{
case 0:
{
lean_object* v_key_2485_; lean_object* v_val_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2498_; 
v_key_2485_ = lean_ctor_get(v___x_2484_, 0);
v_val_2486_ = lean_ctor_get(v___x_2484_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2488_ = v___x_2484_;
v_isShared_2489_ = v_isSharedCheck_2498_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_val_2486_);
lean_inc(v_key_2485_);
lean_dec(v___x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2498_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
uint8_t v___x_2490_; 
lean_inc(v_key_2485_);
v___x_2490_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_2471_, v_x_2474_, v_key_2485_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_del_object(v___x_2488_);
lean_dec(v_val_2486_);
lean_dec(v_key_2485_);
lean_del_object(v___x_2477_);
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
else
{
lean_object* v___x_2493_; 
if (v_isShared_2489_ == 0)
{
v___x_2493_ = v___x_2488_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_key_2485_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_val_2486_);
v___x_2493_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 1);
lean_ctor_set(v___x_2477_, 0, v___x_2493_);
v___x_2495_ = v___x_2477_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
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
}
case 1:
{
lean_object* v_node_2499_; size_t v___x_2500_; 
lean_del_object(v___x_2477_);
v_node_2499_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_node_2499_);
lean_dec_ref(v___x_2484_);
v___x_2500_ = lean_usize_shift_right(v_x_2473_, v___x_2480_);
v_x_2472_ = v_node_2499_;
v_x_2473_ = v___x_2500_;
goto _start;
}
default: 
{
lean_object* v___x_2502_; 
lean_del_object(v___x_2477_);
lean_dec_ref(v_x_2474_);
lean_dec_ref(v___x_2471_);
v___x_2502_ = lean_box(0);
return v___x_2502_;
}
}
}
}
else
{
lean_object* v_ks_2504_; lean_object* v_vs_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_ks_2504_ = lean_ctor_get(v_x_2472_, 0);
lean_inc_ref(v_ks_2504_);
v_vs_2505_ = lean_ctor_get(v_x_2472_, 1);
lean_inc_ref(v_vs_2505_);
lean_dec_ref(v_x_2472_);
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2471_, v_ks_2504_, v_vs_2505_, v___x_2506_, v_x_2474_);
lean_dec_ref(v_vs_2505_);
lean_dec_ref(v_ks_2504_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
size_t v_x_27753__boxed_2512_; lean_object* v_res_2513_; 
v_x_27753__boxed_2512_ = lean_unbox_usize(v_x_2510_);
lean_dec(v_x_2510_);
v_res_2513_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2508_, v_x_2509_, v_x_27753__boxed_2512_, v_x_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2514_, lean_object* v_x_2515_, lean_object* v_x_2516_){
_start:
{
uint64_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
lean_inc_ref(v_x_2516_);
lean_inc_ref(v___x_2514_);
v___x_2517_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_2514_, v_x_2516_);
v___x_2518_ = lean_uint64_to_usize(v___x_2517_);
v___x_2519_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2514_, v_x_2515_, v___x_2518_, v_x_2516_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
lean_object* v_ks_2525_; lean_object* v_vs_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2550_; 
v_ks_2525_ = lean_ctor_get(v_x_2521_, 0);
v_vs_2526_ = lean_ctor_get(v_x_2521_, 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2521_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2528_ = v_x_2521_;
v_isShared_2529_ = v_isSharedCheck_2550_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_vs_2526_);
lean_inc(v_ks_2525_);
lean_dec(v_x_2521_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2550_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = lean_array_get_size(v_ks_2525_);
v___x_2531_ = lean_nat_dec_lt(v_x_2522_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_dec(v_x_2522_);
lean_dec_ref(v___x_2520_);
v___x_2532_ = lean_array_push(v_ks_2525_, v_x_2523_);
v___x_2533_ = lean_array_push(v_vs_2526_, v_x_2524_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2533_);
lean_ctor_set(v___x_2528_, 0, v___x_2532_);
v___x_2535_ = v___x_2528_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
else
{
lean_object* v_k_x27_2537_; uint8_t v___x_2538_; 
v_k_x27_2537_ = lean_array_fget_borrowed(v_ks_2525_, v_x_2522_);
lean_inc(v_k_x27_2537_);
lean_inc_ref(v_x_2523_);
lean_inc_ref(v___x_2520_);
v___x_2538_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_2520_, v_x_2523_, v_k_x27_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2540_; 
if (v_isShared_2529_ == 0)
{
v___x_2540_ = v___x_2528_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_ks_2525_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_vs_2526_);
v___x_2540_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_unsigned_to_nat(1u);
v___x_2542_ = lean_nat_add(v_x_2522_, v___x_2541_);
lean_dec(v_x_2522_);
v_x_2521_ = v___x_2540_;
v_x_2522_ = v___x_2542_;
goto _start;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_dec_ref(v___x_2520_);
v___x_2545_ = lean_array_fset(v_ks_2525_, v_x_2522_, v_x_2523_);
v___x_2546_ = lean_array_fset(v_vs_2526_, v_x_2522_, v_x_2524_);
lean_dec(v_x_2522_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2546_);
lean_ctor_set(v___x_2528_, 0, v___x_2545_);
v___x_2548_ = v___x_2528_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2551_, lean_object* v_n_2552_, lean_object* v_k_2553_, lean_object* v_v_2554_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2551_, v_n_2552_, v___x_2555_, v_k_2553_, v_v_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2558_, lean_object* v_x_2559_, size_t v_x_2560_, size_t v_x_2561_, lean_object* v_x_2562_, lean_object* v_x_2563_){
_start:
{
if (lean_obj_tag(v_x_2559_) == 0)
{
lean_object* v_es_2564_; size_t v___x_2565_; size_t v___x_2566_; size_t v___x_2567_; size_t v___x_2568_; lean_object* v_j_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_es_2564_ = lean_ctor_get(v_x_2559_, 0);
v___x_2565_ = ((size_t)5ULL);
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2568_ = lean_usize_land(v_x_2560_, v___x_2567_);
v_j_2569_ = lean_usize_to_nat(v___x_2568_);
v___x_2570_ = lean_array_get_size(v_es_2564_);
v___x_2571_ = lean_nat_dec_lt(v_j_2569_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_dec(v_j_2569_);
lean_dec(v_x_2563_);
lean_dec_ref(v_x_2562_);
lean_dec_ref(v___x_2558_);
return v_x_2559_;
}
else
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2608_; 
lean_inc_ref(v_es_2564_);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_x_2559_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v_x_2559_, 0);
lean_dec(v_unused_2609_);
v___x_2573_ = v_x_2559_;
v_isShared_2574_ = v_isSharedCheck_2608_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v_x_2559_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2608_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_v_2575_; lean_object* v___x_2576_; lean_object* v_xs_x27_2577_; lean_object* v___y_2579_; 
v_v_2575_ = lean_array_fget(v_es_2564_, v_j_2569_);
v___x_2576_ = lean_box(0);
v_xs_x27_2577_ = lean_array_fset(v_es_2564_, v_j_2569_, v___x_2576_);
switch(lean_obj_tag(v_v_2575_))
{
case 0:
{
lean_object* v_key_2584_; lean_object* v_val_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2595_; 
v_key_2584_ = lean_ctor_get(v_v_2575_, 0);
v_val_2585_ = lean_ctor_get(v_v_2575_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_v_2575_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2587_ = v_v_2575_;
v_isShared_2588_ = v_isSharedCheck_2595_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_val_2585_);
lean_inc(v_key_2584_);
lean_dec(v_v_2575_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2595_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
uint8_t v___x_2589_; 
lean_inc(v_key_2584_);
lean_inc_ref(v_x_2562_);
v___x_2589_ = l_Lean_Meta_Grind_instBEqCongrKey___private__1(v___x_2558_, v_x_2562_, v_key_2584_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2587_);
v___x_2590_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2584_, v_val_2585_, v_x_2562_, v_x_2563_);
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
v___y_2579_ = v___x_2591_;
goto v___jp_2578_;
}
else
{
lean_object* v___x_2593_; 
lean_dec(v_val_2585_);
lean_dec(v_key_2584_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v_x_2563_);
lean_ctor_set(v___x_2587_, 0, v_x_2562_);
v___x_2593_ = v___x_2587_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_x_2562_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_x_2563_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
v___y_2579_ = v___x_2593_;
goto v___jp_2578_;
}
}
}
}
case 1:
{
lean_object* v_node_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2606_; 
v_node_2596_ = lean_ctor_get(v_v_2575_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_v_2575_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2598_ = v_v_2575_;
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_node_2596_);
lean_dec(v_v_2575_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2606_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2600_ = lean_usize_shift_right(v_x_2560_, v___x_2565_);
v___x_2601_ = lean_usize_add(v_x_2561_, v___x_2566_);
v___x_2602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2558_, v_node_2596_, v___x_2600_, v___x_2601_, v_x_2562_, v_x_2563_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2602_);
v___x_2604_ = v___x_2598_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
v___y_2579_ = v___x_2604_;
goto v___jp_2578_;
}
}
}
default: 
{
lean_object* v___x_2607_; 
lean_dec_ref(v___x_2558_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_x_2562_);
lean_ctor_set(v___x_2607_, 1, v_x_2563_);
v___y_2579_ = v___x_2607_;
goto v___jp_2578_;
}
}
v___jp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_array_fset(v_xs_x27_2577_, v_j_2569_, v___y_2579_);
lean_dec(v_j_2569_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2580_);
v___x_2582_ = v___x_2573_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_ks_2610_; lean_object* v_vs_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2631_; 
v_ks_2610_ = lean_ctor_get(v_x_2559_, 0);
v_vs_2611_ = lean_ctor_get(v_x_2559_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_x_2559_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2613_ = v_x_2559_;
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_vs_2611_);
lean_inc(v_ks_2610_);
lean_dec(v_x_2559_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_ks_2610_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_vs_2611_);
v___x_2616_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v_newNode_2617_; uint8_t v___y_2619_; size_t v___x_2625_; uint8_t v___x_2626_; 
lean_inc_ref(v___x_2558_);
v_newNode_2617_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2558_, v___x_2616_, v_x_2562_, v_x_2563_);
v___x_2625_ = ((size_t)7ULL);
v___x_2626_ = lean_usize_dec_le(v___x_2625_, v_x_2561_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2627_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2617_);
v___x_2628_ = lean_unsigned_to_nat(4u);
v___x_2629_ = lean_nat_dec_lt(v___x_2627_, v___x_2628_);
lean_dec(v___x_2627_);
v___y_2619_ = v___x_2629_;
goto v___jp_2618_;
}
else
{
v___y_2619_ = v___x_2626_;
goto v___jp_2618_;
}
v___jp_2618_:
{
if (v___y_2619_ == 0)
{
lean_object* v_ks_2620_; lean_object* v_vs_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_ks_2620_ = lean_ctor_get(v_newNode_2617_, 0);
lean_inc_ref(v_ks_2620_);
v_vs_2621_ = lean_ctor_get(v_newNode_2617_, 1);
lean_inc_ref(v_vs_2621_);
lean_dec_ref(v_newNode_2617_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2558_, v_x_2561_, v_ks_2620_, v_vs_2621_, v___x_2622_, v___x_2623_);
lean_dec_ref(v_vs_2621_);
lean_dec_ref(v_ks_2620_);
return v___x_2624_;
}
else
{
lean_dec_ref(v___x_2558_);
return v_newNode_2617_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2632_, size_t v_depth_2633_, lean_object* v_keys_2634_, lean_object* v_vals_2635_, lean_object* v_i_2636_, lean_object* v_entries_2637_){
_start:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = lean_array_get_size(v_keys_2634_);
v___x_2639_ = lean_nat_dec_lt(v_i_2636_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec(v_i_2636_);
lean_dec_ref(v___x_2632_);
return v_entries_2637_;
}
else
{
lean_object* v_k_2640_; lean_object* v_v_2641_; uint64_t v___x_2642_; size_t v_h_2643_; size_t v___x_2644_; lean_object* v___x_2645_; size_t v___x_2646_; size_t v___x_2647_; size_t v___x_2648_; size_t v_h_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_k_2640_ = lean_array_fget_borrowed(v_keys_2634_, v_i_2636_);
v_v_2641_ = lean_array_fget_borrowed(v_vals_2635_, v_i_2636_);
lean_inc(v_k_2640_);
lean_inc_ref(v___x_2632_);
v___x_2642_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_2632_, v_k_2640_);
v_h_2643_ = lean_uint64_to_usize(v___x_2642_);
v___x_2644_ = ((size_t)5ULL);
v___x_2645_ = lean_unsigned_to_nat(1u);
v___x_2646_ = ((size_t)1ULL);
v___x_2647_ = lean_usize_sub(v_depth_2633_, v___x_2646_);
v___x_2648_ = lean_usize_mul(v___x_2644_, v___x_2647_);
v_h_2649_ = lean_usize_shift_right(v_h_2643_, v___x_2648_);
v___x_2650_ = lean_nat_add(v_i_2636_, v___x_2645_);
lean_dec(v_i_2636_);
lean_inc(v_v_2641_);
lean_inc(v_k_2640_);
lean_inc_ref(v___x_2632_);
v___x_2651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2632_, v_entries_2637_, v_h_2649_, v_depth_2633_, v_k_2640_, v_v_2641_);
v_i_2636_ = v___x_2650_;
v_entries_2637_ = v___x_2651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2653_, lean_object* v_depth_2654_, lean_object* v_keys_2655_, lean_object* v_vals_2656_, lean_object* v_i_2657_, lean_object* v_entries_2658_){
_start:
{
size_t v_depth_boxed_2659_; lean_object* v_res_2660_; 
v_depth_boxed_2659_ = lean_unbox_usize(v_depth_2654_);
lean_dec(v_depth_2654_);
v_res_2660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2653_, v_depth_boxed_2659_, v_keys_2655_, v_vals_2656_, v_i_2657_, v_entries_2658_);
lean_dec_ref(v_vals_2656_);
lean_dec_ref(v_keys_2655_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
size_t v_x_27930__boxed_2667_; size_t v_x_27931__boxed_2668_; lean_object* v_res_2669_; 
v_x_27930__boxed_2667_ = lean_unbox_usize(v_x_2663_);
lean_dec(v_x_2663_);
v_x_27931__boxed_2668_ = lean_unbox_usize(v_x_2664_);
lean_dec(v_x_2664_);
v_res_2669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2661_, v_x_2662_, v_x_27930__boxed_2667_, v_x_27931__boxed_2668_, v_x_2665_, v_x_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
uint64_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
lean_inc_ref(v_x_2672_);
lean_inc_ref(v___x_2670_);
v___x_2674_ = l_Lean_Meta_Grind_instHashableCongrKey___private__1(v___x_2670_, v_x_2672_);
v___x_2675_ = lean_uint64_to_usize(v___x_2674_);
v___x_2676_ = ((size_t)1ULL);
v___x_2677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2670_, v_x_2671_, v___x_2675_, v___x_2676_, v_x_2672_, v_x_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2682_, lean_object* v_rootNew_2683_, uint8_t v_a_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; lean_object* v_snd_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2860_; 
v___x_2693_ = lean_st_ref_get(v___y_2686_);
v_snd_2694_ = lean_ctor_get(v_b_2685_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_b_2685_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v_b_2685_, 0);
lean_dec(v_unused_2861_);
v___x_2696_ = v_b_2685_;
v_isShared_2697_ = v_isSharedCheck_2860_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snd_2694_);
lean_dec(v_b_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2860_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; 
lean_inc(v_snd_2694_);
v___x_2698_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2693_, v_snd_2694_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2851_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2851_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2851_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_self_2703_; lean_object* v_next_2704_; lean_object* v_congr_2705_; lean_object* v_target_x3f_2706_; lean_object* v_proof_x3f_2707_; uint8_t v_flipped_2708_; lean_object* v_size_2709_; uint8_t v_interpreted_2710_; uint8_t v_ctor_2711_; uint8_t v_hasLambdas_2712_; uint8_t v_heqProofs_2713_; lean_object* v_idx_2714_; lean_object* v_generation_2715_; lean_object* v_mt_2716_; lean_object* v_sTerms_2717_; uint8_t v_funCC_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2849_; 
v_self_2703_ = lean_ctor_get(v_a_2699_, 0);
v_next_2704_ = lean_ctor_get(v_a_2699_, 1);
v_congr_2705_ = lean_ctor_get(v_a_2699_, 3);
v_target_x3f_2706_ = lean_ctor_get(v_a_2699_, 4);
v_proof_x3f_2707_ = lean_ctor_get(v_a_2699_, 5);
v_flipped_2708_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11);
v_size_2709_ = lean_ctor_get(v_a_2699_, 6);
v_interpreted_2710_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11 + 1);
v_ctor_2711_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11 + 2);
v_hasLambdas_2712_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11 + 3);
v_heqProofs_2713_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11 + 4);
v_idx_2714_ = lean_ctor_get(v_a_2699_, 7);
v_generation_2715_ = lean_ctor_get(v_a_2699_, 8);
v_mt_2716_ = lean_ctor_get(v_a_2699_, 9);
v_sTerms_2717_ = lean_ctor_get(v_a_2699_, 10);
v_funCC_2718_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*11 + 5);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_a_2699_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_a_2699_, 2);
lean_dec(v_unused_2850_);
v___x_2720_ = v_a_2699_;
v_isShared_2721_ = v_isSharedCheck_2849_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_sTerms_2717_);
lean_inc(v_mt_2716_);
lean_inc(v_generation_2715_);
lean_inc(v_idx_2714_);
lean_inc(v_size_2709_);
lean_inc(v_proof_x3f_2707_);
lean_inc(v_target_x3f_2706_);
lean_inc(v_congr_2705_);
lean_inc(v_next_2704_);
lean_inc(v_self_2703_);
lean_dec(v_a_2699_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2849_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___y_2737_; lean_object* v___x_2747_; 
v___x_2722_ = lean_box(0);
lean_inc(v_sTerms_2717_);
lean_inc(v_mt_2716_);
lean_inc(v_generation_2715_);
lean_inc(v_idx_2714_);
lean_inc(v_size_2709_);
lean_inc(v_proof_x3f_2707_);
lean_inc(v_target_x3f_2706_);
lean_inc_ref(v_rootNew_2683_);
lean_inc_ref(v_next_2704_);
lean_inc_ref(v_self_2703_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 2, v_rootNew_2683_);
v___x_2747_ = v___x_2720_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_self_2703_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_next_2704_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_rootNew_2683_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_congr_2705_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_target_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2848_, 5, v_proof_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2848_, 6, v_size_2709_);
lean_ctor_set(v_reuseFailAlloc_2848_, 7, v_idx_2714_);
lean_ctor_set(v_reuseFailAlloc_2848_, 8, v_generation_2715_);
lean_ctor_set(v_reuseFailAlloc_2848_, 9, v_mt_2716_);
lean_ctor_set(v_reuseFailAlloc_2848_, 10, v_sTerms_2717_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11, v_flipped_2708_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11 + 1, v_interpreted_2710_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11 + 2, v_ctor_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11 + 3, v_hasLambdas_2712_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11 + 4, v_heqProofs_2713_);
lean_ctor_set_uint8(v_reuseFailAlloc_2848_, sizeof(void*)*11 + 5, v_funCC_2718_);
v___x_2747_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2746_;
}
v___jp_2723_:
{
uint8_t v___x_2724_; 
v___x_2724_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2704_, v_lhs_2682_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2726_; 
lean_del_object(v___x_2701_);
lean_dec(v_snd_2694_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v_next_2704_);
lean_ctor_set(v___x_2696_, 0, v___x_2722_);
v___x_2726_ = v___x_2696_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_next_2704_);
v___x_2726_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
v_b_2685_ = v___x_2726_;
goto _start;
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
lean_dec_ref(v_next_2704_);
lean_dec_ref(v_rootNew_2683_);
v___x_2729_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2729_);
v___x_2731_ = v___x_2696_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_snd_2694_);
v___x_2731_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v___x_2731_);
v___x_2733_ = v___x_2701_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
v___jp_2736_:
{
if (lean_obj_tag(v___y_2737_) == 0)
{
lean_dec_ref(v___y_2737_);
goto v___jp_2723_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_next_2704_);
lean_del_object(v___x_2701_);
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_dec_ref(v_rootNew_2683_);
v_a_2738_ = lean_ctor_get(v___y_2737_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___y_2737_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___y_2737_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___y_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
lean_inc_ref(v___x_2747_);
lean_inc_ref(v_self_2703_);
v___x_2748_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2703_, v___x_2747_, v___y_2686_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_dec_ref(v___x_2748_);
if (v_a_2684_ == 0)
{
lean_dec_ref(v___x_2747_);
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
goto v___jp_2723_;
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2749_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2750_ = lean_unsigned_to_nat(3u);
v___x_2751_ = l_Lean_Expr_isAppOfArity(v_self_2703_, v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_dec_ref(v___x_2747_);
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
goto v___jp_2723_;
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2747_);
lean_dec_ref(v___x_2747_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v_toGoalState_2754_; lean_object* v_enodeMap_2755_; lean_object* v_congrTable_2756_; lean_object* v___x_2757_; 
v___x_2753_ = lean_st_ref_get(v___y_2686_);
v_toGoalState_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_ref(v_toGoalState_2754_);
lean_dec(v___x_2753_);
v_enodeMap_2755_ = lean_ctor_get(v_toGoalState_2754_, 2);
lean_inc_ref(v_enodeMap_2755_);
v_congrTable_2756_ = lean_ctor_get(v_toGoalState_2754_, 5);
lean_inc_ref(v_congrTable_2756_);
lean_dec_ref(v_toGoalState_2754_);
lean_inc_ref(v_self_2703_);
v___x_2757_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2755_, v_congrTable_2756_, v_self_2703_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
goto v___jp_2723_;
}
else
{
lean_object* v_val_2758_; lean_object* v_fst_2759_; lean_object* v___x_2760_; 
v_val_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_val_2758_);
lean_dec_ref(v___x_2757_);
v_fst_2759_ = lean_ctor_get(v_val_2758_, 0);
lean_inc(v_fst_2759_);
lean_dec(v_val_2758_);
v___x_2760_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2759_, v___y_2687_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; uint8_t v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = lean_unbox(v_a_2761_);
lean_dec(v_a_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v_toGoalState_2764_; lean_object* v_mvarId_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2839_; 
v___x_2763_ = lean_st_ref_take(v___y_2686_);
v_toGoalState_2764_ = lean_ctor_get(v___x_2763_, 0);
v_mvarId_2765_ = lean_ctor_get(v___x_2763_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2839_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_mvarId_2765_);
lean_inc(v_toGoalState_2764_);
lean_dec(v___x_2763_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2839_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v_nextDeclIdx_2769_; lean_object* v_canon_2770_; lean_object* v_enodeMap_2771_; lean_object* v_exprs_2772_; lean_object* v_parents_2773_; lean_object* v_congrTable_2774_; lean_object* v_appMap_2775_; lean_object* v_indicesFound_2776_; lean_object* v_newFacts_2777_; uint8_t v_inconsistent_2778_; lean_object* v_nextIdx_2779_; lean_object* v_newRawFacts_2780_; lean_object* v_facts_2781_; lean_object* v_extThms_2782_; lean_object* v_ematch_2783_; lean_object* v_inj_2784_; lean_object* v_split_2785_; lean_object* v_clean_2786_; lean_object* v_sstates_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2838_; 
v_nextDeclIdx_2769_ = lean_ctor_get(v_toGoalState_2764_, 0);
v_canon_2770_ = lean_ctor_get(v_toGoalState_2764_, 1);
v_enodeMap_2771_ = lean_ctor_get(v_toGoalState_2764_, 2);
v_exprs_2772_ = lean_ctor_get(v_toGoalState_2764_, 3);
v_parents_2773_ = lean_ctor_get(v_toGoalState_2764_, 4);
v_congrTable_2774_ = lean_ctor_get(v_toGoalState_2764_, 5);
v_appMap_2775_ = lean_ctor_get(v_toGoalState_2764_, 6);
v_indicesFound_2776_ = lean_ctor_get(v_toGoalState_2764_, 7);
v_newFacts_2777_ = lean_ctor_get(v_toGoalState_2764_, 8);
v_inconsistent_2778_ = lean_ctor_get_uint8(v_toGoalState_2764_, sizeof(void*)*18);
v_nextIdx_2779_ = lean_ctor_get(v_toGoalState_2764_, 9);
v_newRawFacts_2780_ = lean_ctor_get(v_toGoalState_2764_, 10);
v_facts_2781_ = lean_ctor_get(v_toGoalState_2764_, 11);
v_extThms_2782_ = lean_ctor_get(v_toGoalState_2764_, 12);
v_ematch_2783_ = lean_ctor_get(v_toGoalState_2764_, 13);
v_inj_2784_ = lean_ctor_get(v_toGoalState_2764_, 14);
v_split_2785_ = lean_ctor_get(v_toGoalState_2764_, 15);
v_clean_2786_ = lean_ctor_get(v_toGoalState_2764_, 16);
v_sstates_2787_ = lean_ctor_get(v_toGoalState_2764_, 17);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_toGoalState_2764_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2789_ = v_toGoalState_2764_;
v_isShared_2790_ = v_isSharedCheck_2838_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_sstates_2787_);
lean_inc(v_clean_2786_);
lean_inc(v_split_2785_);
lean_inc(v_inj_2784_);
lean_inc(v_ematch_2783_);
lean_inc(v_extThms_2782_);
lean_inc(v_facts_2781_);
lean_inc(v_newRawFacts_2780_);
lean_inc(v_nextIdx_2779_);
lean_inc(v_newFacts_2777_);
lean_inc(v_indicesFound_2776_);
lean_inc(v_appMap_2775_);
lean_inc(v_congrTable_2774_);
lean_inc(v_parents_2773_);
lean_inc(v_exprs_2772_);
lean_inc(v_enodeMap_2771_);
lean_inc(v_canon_2770_);
lean_inc(v_nextDeclIdx_2769_);
lean_dec(v_toGoalState_2764_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2838_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2791_ = lean_box(0);
lean_inc_ref(v_self_2703_);
lean_inc_ref(v_enodeMap_2771_);
v___x_2792_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_2771_, v_congrTable_2774_, v_self_2703_, v___x_2791_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 5, v___x_2792_);
v___x_2794_ = v___x_2789_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_nextDeclIdx_2769_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_canon_2770_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_enodeMap_2771_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_exprs_2772_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_parents_2773_);
lean_ctor_set(v_reuseFailAlloc_2837_, 5, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2837_, 6, v_appMap_2775_);
lean_ctor_set(v_reuseFailAlloc_2837_, 7, v_indicesFound_2776_);
lean_ctor_set(v_reuseFailAlloc_2837_, 8, v_newFacts_2777_);
lean_ctor_set(v_reuseFailAlloc_2837_, 9, v_nextIdx_2779_);
lean_ctor_set(v_reuseFailAlloc_2837_, 10, v_newRawFacts_2780_);
lean_ctor_set(v_reuseFailAlloc_2837_, 11, v_facts_2781_);
lean_ctor_set(v_reuseFailAlloc_2837_, 12, v_extThms_2782_);
lean_ctor_set(v_reuseFailAlloc_2837_, 13, v_ematch_2783_);
lean_ctor_set(v_reuseFailAlloc_2837_, 14, v_inj_2784_);
lean_ctor_set(v_reuseFailAlloc_2837_, 15, v_split_2785_);
lean_ctor_set(v_reuseFailAlloc_2837_, 16, v_clean_2786_);
lean_ctor_set(v_reuseFailAlloc_2837_, 17, v_sstates_2787_);
lean_ctor_set_uint8(v_reuseFailAlloc_2837_, sizeof(void*)*18, v_inconsistent_2778_);
v___x_2794_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2796_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2794_);
v___x_2796_ = v___x_2767_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_mvarId_2765_);
v___x_2796_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_st_ref_set(v___y_2686_, v___x_2796_);
lean_inc_ref(v_rootNew_2683_);
lean_inc_ref(v_next_2704_);
lean_inc_ref_n(v_self_2703_, 2);
v___x_2798_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_2798_, 0, v_self_2703_);
lean_ctor_set(v___x_2798_, 1, v_next_2704_);
lean_ctor_set(v___x_2798_, 2, v_rootNew_2683_);
lean_ctor_set(v___x_2798_, 3, v_self_2703_);
lean_ctor_set(v___x_2798_, 4, v_target_x3f_2706_);
lean_ctor_set(v___x_2798_, 5, v_proof_x3f_2707_);
lean_ctor_set(v___x_2798_, 6, v_size_2709_);
lean_ctor_set(v___x_2798_, 7, v_idx_2714_);
lean_ctor_set(v___x_2798_, 8, v_generation_2715_);
lean_ctor_set(v___x_2798_, 9, v_mt_2716_);
lean_ctor_set(v___x_2798_, 10, v_sTerms_2717_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11, v_flipped_2708_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11 + 1, v_interpreted_2710_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11 + 2, v_ctor_2711_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11 + 3, v_hasLambdas_2712_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11 + 4, v_heqProofs_2713_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*11 + 5, v_funCC_2718_);
lean_inc_ref(v_self_2703_);
v___x_2799_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2703_, v___x_2798_, v___y_2686_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v___x_2799_);
v___x_2800_ = lean_st_ref_get(v___y_2686_);
lean_inc(v_fst_2759_);
v___x_2801_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2800_, v_fst_2759_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v_self_2803_; lean_object* v_next_2804_; lean_object* v_root_2805_; lean_object* v_target_x3f_2806_; lean_object* v_proof_x3f_2807_; uint8_t v_flipped_2808_; lean_object* v_size_2809_; uint8_t v_interpreted_2810_; uint8_t v_ctor_2811_; uint8_t v_hasLambdas_2812_; uint8_t v_heqProofs_2813_; lean_object* v_idx_2814_; lean_object* v_generation_2815_; lean_object* v_mt_2816_; lean_object* v_sTerms_2817_; uint8_t v_funCC_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v_self_2803_ = lean_ctor_get(v_a_2802_, 0);
v_next_2804_ = lean_ctor_get(v_a_2802_, 1);
v_root_2805_ = lean_ctor_get(v_a_2802_, 2);
v_target_x3f_2806_ = lean_ctor_get(v_a_2802_, 4);
v_proof_x3f_2807_ = lean_ctor_get(v_a_2802_, 5);
v_flipped_2808_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11);
v_size_2809_ = lean_ctor_get(v_a_2802_, 6);
v_interpreted_2810_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11 + 1);
v_ctor_2811_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11 + 2);
v_hasLambdas_2812_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11 + 3);
v_heqProofs_2813_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11 + 4);
v_idx_2814_ = lean_ctor_get(v_a_2802_, 7);
v_generation_2815_ = lean_ctor_get(v_a_2802_, 8);
v_mt_2816_ = lean_ctor_get(v_a_2802_, 9);
v_sTerms_2817_ = lean_ctor_get(v_a_2802_, 10);
v_funCC_2818_ = lean_ctor_get_uint8(v_a_2802_, sizeof(void*)*11 + 5);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_a_2802_, 3);
lean_dec(v_unused_2827_);
v___x_2820_ = v_a_2802_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_sTerms_2817_);
lean_inc(v_mt_2816_);
lean_inc(v_generation_2815_);
lean_inc(v_idx_2814_);
lean_inc(v_size_2809_);
lean_inc(v_proof_x3f_2807_);
lean_inc(v_target_x3f_2806_);
lean_inc(v_root_2805_);
lean_inc(v_next_2804_);
lean_inc(v_self_2803_);
lean_dec(v_a_2802_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 3, v_self_2703_);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_self_2803_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_next_2804_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_root_2805_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_self_2703_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_target_x3f_2806_);
lean_ctor_set(v_reuseFailAlloc_2825_, 5, v_proof_x3f_2807_);
lean_ctor_set(v_reuseFailAlloc_2825_, 6, v_size_2809_);
lean_ctor_set(v_reuseFailAlloc_2825_, 7, v_idx_2814_);
lean_ctor_set(v_reuseFailAlloc_2825_, 8, v_generation_2815_);
lean_ctor_set(v_reuseFailAlloc_2825_, 9, v_mt_2816_);
lean_ctor_set(v_reuseFailAlloc_2825_, 10, v_sTerms_2817_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11, v_flipped_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11 + 1, v_interpreted_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11 + 2, v_ctor_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11 + 3, v_hasLambdas_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11 + 4, v_heqProofs_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2825_, sizeof(void*)*11 + 5, v_funCC_2818_);
v___x_2823_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2759_, v___x_2823_, v___y_2686_);
v___y_2737_ = v___x_2824_;
goto v___jp_2736_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_fst_2759_);
lean_dec_ref(v_next_2704_);
lean_dec_ref(v_self_2703_);
lean_del_object(v___x_2701_);
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_dec_ref(v_rootNew_2683_);
v_a_2828_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2801_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2801_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_dec(v_fst_2759_);
lean_dec_ref(v_self_2703_);
v___y_2737_ = v___x_2799_;
goto v___jp_2736_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2759_);
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
goto v___jp_2723_;
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_fst_2759_);
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_next_2704_);
lean_dec_ref(v_self_2703_);
lean_del_object(v___x_2701_);
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_dec_ref(v_rootNew_2683_);
v_a_2840_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2760_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2760_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
else
{
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
goto v___jp_2723_;
}
}
}
}
else
{
lean_dec_ref(v___x_2747_);
lean_dec(v_sTerms_2717_);
lean_dec(v_mt_2716_);
lean_dec(v_generation_2715_);
lean_dec(v_idx_2714_);
lean_dec(v_size_2709_);
lean_dec(v_proof_x3f_2707_);
lean_dec(v_target_x3f_2706_);
lean_dec_ref(v_self_2703_);
v___y_2737_ = v___x_2748_;
goto v___jp_2736_;
}
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_del_object(v___x_2696_);
lean_dec(v_snd_2694_);
lean_dec_ref(v_rootNew_2683_);
v_a_2852_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2698_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2698_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_2862_, lean_object* v_rootNew_2863_, lean_object* v_a_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
uint8_t v_a_28114__boxed_2873_; lean_object* v_res_2874_; 
v_a_28114__boxed_2873_ = lean_unbox(v_a_2864_);
v_res_2874_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_2862_, v_rootNew_2863_, v_a_28114__boxed_2873_, v_b_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v_lhs_2862_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_2875_, lean_object* v_rootNew_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_2876_, v_a_2881_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = lean_box(0);
lean_inc_ref(v_lhs_2875_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v_lhs_2875_);
v___x_2892_ = lean_unbox(v_a_2889_);
lean_dec(v_a_2889_);
v___x_2893_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_2875_, v_rootNew_2876_, v___x_2892_, v___x_2891_, v_a_2877_, v_a_2881_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec_ref(v_lhs_2875_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2907_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2907_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2907_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v_fst_2898_; 
v_fst_2898_ = lean_ctor_get(v_a_2894_, 0);
lean_inc(v_fst_2898_);
lean_dec(v_a_2894_);
if (lean_obj_tag(v_fst_2898_) == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = lean_box(0);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2899_);
v___x_2901_ = v___x_2896_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2905_; 
v_val_2903_ = lean_ctor_get(v_fst_2898_, 0);
lean_inc(v_val_2903_);
lean_dec_ref(v_fst_2898_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v_val_2903_);
v___x_2905_ = v___x_2896_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_val_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
v_a_2908_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2893_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2893_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_rootNew_2876_);
lean_dec_ref(v_lhs_2875_);
v_a_2916_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2888_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2888_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_2924_, lean_object* v_rootNew_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_2924_, v_rootNew_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec(v_a_2926_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_2938_, lean_object* v_00_u03b2_2939_, lean_object* v_x_2940_, lean_object* v_x_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2938_, v_x_2940_, v_x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2943_, v_x_2945_, v_x_2946_, v_x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_2949_, lean_object* v_rootNew_2950_, uint8_t v_a_2951_, lean_object* v_b_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_2949_, v_rootNew_2950_, v_a_2951_, v_b_2952_, v___y_2953_, v___y_2957_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_2965_, lean_object* v_rootNew_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v_a_28492__boxed_2980_; lean_object* v_res_2981_; 
v_a_28492__boxed_2980_ = lean_unbox(v_a_2967_);
v_res_2981_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_2965_, v_rootNew_2966_, v_a_28492__boxed_2980_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v_lhs_2965_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_2982_, lean_object* v_00_u03b2_2983_, lean_object* v_x_2984_, size_t v_x_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2982_, v_x_2984_, v_x_2985_, v_x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_2988_, lean_object* v_00_u03b2_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_){
_start:
{
size_t v_x_28532__boxed_2993_; lean_object* v_res_2994_; 
v_x_28532__boxed_2993_ = lean_unbox_usize(v_x_2991_);
lean_dec(v_x_2991_);
v_res_2994_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_2988_, v_00_u03b2_2989_, v_x_2990_, v_x_28532__boxed_2993_, v_x_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_x_2997_, size_t v_x_2998_, size_t v_x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2995_, v_x_2997_, v_x_2998_, v_x_2999_, v_x_3000_, v_x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3003_, lean_object* v_00_u03b2_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_x_3009_){
_start:
{
size_t v_x_28546__boxed_3010_; size_t v_x_28547__boxed_3011_; lean_object* v_res_3012_; 
v_x_28546__boxed_3010_ = lean_unbox_usize(v_x_3006_);
lean_dec(v_x_3006_);
v_x_28547__boxed_3011_ = lean_unbox_usize(v_x_3007_);
lean_dec(v_x_3007_);
v_res_3012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3003_, v_00_u03b2_3004_, v_x_3005_, v_x_28546__boxed_3010_, v_x_28547__boxed_3011_, v_x_3008_, v_x_3009_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3013_, lean_object* v_00_u03b2_3014_, lean_object* v_keys_3015_, lean_object* v_vals_3016_, lean_object* v_heq_3017_, lean_object* v_i_3018_, lean_object* v_k_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3013_, v_keys_3015_, v_vals_3016_, v_i_3018_, v_k_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3021_, lean_object* v_00_u03b2_3022_, lean_object* v_keys_3023_, lean_object* v_vals_3024_, lean_object* v_heq_3025_, lean_object* v_i_3026_, lean_object* v_k_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3021_, v_00_u03b2_3022_, v_keys_3023_, v_vals_3024_, v_heq_3025_, v_i_3026_, v_k_3027_);
lean_dec_ref(v_vals_3024_);
lean_dec_ref(v_keys_3023_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3029_, lean_object* v_00_u03b2_3030_, lean_object* v_n_3031_, lean_object* v_k_3032_, lean_object* v_v_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3029_, v_n_3031_, v_k_3032_, v_v_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3035_, lean_object* v_00_u03b2_3036_, size_t v_depth_3037_, lean_object* v_keys_3038_, lean_object* v_vals_3039_, lean_object* v_heq_3040_, lean_object* v_i_3041_, lean_object* v_entries_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3035_, v_depth_3037_, v_keys_3038_, v_vals_3039_, v_i_3041_, v_entries_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3044_, lean_object* v_00_u03b2_3045_, lean_object* v_depth_3046_, lean_object* v_keys_3047_, lean_object* v_vals_3048_, lean_object* v_heq_3049_, lean_object* v_i_3050_, lean_object* v_entries_3051_){
_start:
{
size_t v_depth_boxed_3052_; lean_object* v_res_3053_; 
v_depth_boxed_3052_ = lean_unbox_usize(v_depth_3046_);
lean_dec(v_depth_3046_);
v_res_3053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3044_, v_00_u03b2_3045_, v_depth_boxed_3052_, v_keys_3047_, v_vals_3048_, v_heq_3049_, v_i_3050_, v_entries_3051_);
lean_dec_ref(v_vals_3048_);
lean_dec_ref(v_keys_3047_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3054_, lean_object* v_00_u03b2_3055_, lean_object* v_x_3056_, lean_object* v_x_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3054_, v_x_3056_, v_x_3057_, v_x_3058_, v_x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
if (lean_obj_tag(v_as_x27_3061_) == 0)
{
lean_object* v___x_3074_; 
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_b_3062_);
return v___x_3074_;
}
else
{
lean_object* v_head_3075_; lean_object* v_tail_3076_; lean_object* v___x_3077_; 
v_head_3075_ = lean_ctor_get(v_as_x27_3061_, 0);
lean_inc(v_head_3075_);
v_tail_3076_ = lean_ctor_get(v_as_x27_3061_, 1);
lean_inc(v_tail_3076_);
lean_dec_ref(v_as_x27_3061_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
lean_inc(v___y_3070_);
lean_inc_ref(v___y_3069_);
lean_inc(v___y_3068_);
lean_inc_ref(v___y_3067_);
lean_inc(v___y_3066_);
lean_inc_ref(v___y_3065_);
lean_inc(v___y_3064_);
lean_inc(v___y_3063_);
v___x_3077_ = l_Lean_Meta_Grind_propagateUp(v_head_3075_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v___x_3078_; 
lean_dec_ref(v___x_3077_);
v___x_3078_ = lean_box(0);
v_as_x27_3061_ = v_tail_3076_;
v_b_3062_ = v___x_3078_;
goto _start;
}
else
{
lean_dec(v_tail_3076_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
return v___x_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3080_, v_b_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3094_, lean_object* v_b_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
if (lean_obj_tag(v_as_x27_3094_) == 0)
{
lean_object* v___x_3107_; 
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec(v___y_3096_);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_b_3095_);
return v___x_3107_;
}
else
{
lean_object* v_head_3108_; lean_object* v_tail_3109_; lean_object* v___x_3110_; 
v_head_3108_ = lean_ctor_get(v_as_x27_3094_, 0);
lean_inc(v_head_3108_);
v_tail_3109_ = lean_ctor_get(v_as_x27_3094_, 1);
lean_inc(v_tail_3109_);
lean_dec_ref(v_as_x27_3094_);
lean_inc(v___y_3105_);
lean_inc_ref(v___y_3104_);
lean_inc(v___y_3103_);
lean_inc_ref(v___y_3102_);
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
lean_inc(v___y_3099_);
lean_inc_ref(v___y_3098_);
lean_inc(v___y_3097_);
lean_inc(v___y_3096_);
v___x_3110_ = l_Lean_Meta_Grind_propagateDown(v_head_3108_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3111_; 
lean_dec_ref(v___x_3110_);
v___x_3111_ = lean_box(0);
v_as_x27_3094_ = v_tail_3109_;
v_b_3095_ = v___x_3111_;
goto _start;
}
else
{
lean_dec(v_tail_3109_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec(v___y_3096_);
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3113_, lean_object* v_b_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3113_, v_b_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v_res_3126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1));
v___x_3132_ = l_Lean_stringToMessageData(v___x_3131_);
return v___x_3132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5));
v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3142_, uint8_t v_isHEq_3143_, lean_object* v_lhs_3144_, lean_object* v_rhs_3145_, lean_object* v_lhsNode_3146_, lean_object* v_rhsNode_3147_, lean_object* v_lhsRoot_3148_, lean_object* v_rhsRoot_3149_, uint8_t v_flipped_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; uint8_t v___y_3215_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; uint8_t v___y_3249_; uint8_t v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; uint8_t v___y_3324_; lean_object* v___y_3325_; uint8_t v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v_cls_3396_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v_fns_u2082_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_fns_u2081_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___x_3592_; lean_object* v_a_3593_; uint8_t v___x_3594_; 
v_cls_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3592_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3396_, v_a_3159_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
v___x_3594_ = lean_unbox(v_a_3593_);
lean_dec(v_a_3593_);
if (v___x_3594_ == 0)
{
v___y_3513_ = v_a_3151_;
v___y_3514_ = v_a_3152_;
v___y_3515_ = v_a_3153_;
v___y_3516_ = v_a_3154_;
v___y_3517_ = v_a_3155_;
v___y_3518_ = v_a_3156_;
v___y_3519_ = v_a_3157_;
v___y_3520_ = v_a_3158_;
v___y_3521_ = v_a_3159_;
v___y_3522_ = v_a_3160_;
goto v___jp_3512_;
}
else
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_Meta_Grind_updateLastTag(v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3596_; 
lean_dec_ref(v___x_3595_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
lean_inc_ref(v_a_3157_);
lean_inc_ref(v_lhs_3144_);
v___x_3596_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3144_, v_a_3151_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3596_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
lean_inc_ref(v_a_3157_);
lean_inc_ref(v_rhs_3145_);
v___x_3598_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3145_, v_a_3151_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v_a_3597_);
v___x_3602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v_a_3599_);
v___x_3605_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_cls_3396_, v___x_3604_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_dec_ref(v___x_3605_);
v___y_3513_ = v_a_3151_;
v___y_3514_ = v_a_3152_;
v___y_3515_ = v_a_3153_;
v___y_3516_ = v_a_3154_;
v___y_3517_ = v_a_3155_;
v___y_3518_ = v_a_3156_;
v___y_3519_ = v_a_3157_;
v___y_3520_ = v_a_3158_;
v___y_3521_ = v_a_3159_;
v___y_3522_ = v_a_3160_;
goto v___jp_3512_;
}
else
{
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhsNode_3146_);
lean_dec_ref(v_rhs_3145_);
lean_dec_ref(v_lhs_3144_);
lean_dec_ref(v_proof_3142_);
return v___x_3605_;
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_a_3597_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhsNode_3146_);
lean_dec_ref(v_rhs_3145_);
lean_dec_ref(v_lhs_3144_);
lean_dec_ref(v_proof_3142_);
v_a_3606_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3598_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3598_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhsNode_3146_);
lean_dec_ref(v_rhs_3145_);
lean_dec_ref(v_lhs_3144_);
lean_dec_ref(v_proof_3142_);
v_a_3614_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3596_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3596_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhsNode_3146_);
lean_dec_ref(v_rhs_3145_);
lean_dec_ref(v_lhs_3144_);
lean_dec_ref(v_proof_3142_);
return v___x_3595_;
}
}
v___jp_3162_:
{
lean_object* v___x_3179_; 
v___x_3179_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3169_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3205_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3205_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3205_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
uint8_t v___x_3184_; 
v___x_3184_ = lean_unbox(v_a_3180_);
lean_dec(v_a_3180_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_del_object(v___x_3182_);
v___x_3185_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3168_);
lean_dec(v___y_3168_);
v___x_3186_ = lean_box(0);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
lean_inc(v___y_3170_);
lean_inc(v___y_3169_);
v___x_3187_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3185_, v___x_3186_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v___x_3188_; 
lean_dec_ref(v___x_3187_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
lean_inc(v___y_3170_);
lean_inc(v___y_3169_);
lean_inc(v___y_3165_);
v___x_3188_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3165_, v___x_3186_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v___x_3188_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
lean_inc(v___y_3170_);
lean_inc(v___y_3169_);
v___x_3189_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3166_, v___y_3163_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3166_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v___x_3189_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
lean_inc(v___y_3170_);
lean_inc(v___y_3169_);
v___x_3190_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3167_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3199_; 
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3200_);
v___x_3192_ = v___x_3190_;
v_isShared_3193_ = v_isSharedCheck_3199_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v___x_3190_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3199_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
uint8_t v___x_3194_; 
v___x_3194_ = l_Lean_Expr_isTrue(v___y_3164_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3196_; 
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3165_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3186_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3186_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
else
{
lean_object* v___x_3198_; 
lean_del_object(v___x_3192_);
v___x_3198_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3165_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3165_);
return v___x_3198_;
}
}
}
else
{
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v___x_3190_;
}
}
else
{
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3167_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v___x_3189_;
}
}
else
{
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v___x_3188_;
}
}
else
{
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v___x_3187_;
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v___y_3163_);
v___x_3201_ = lean_box(0);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3201_);
v___x_3203_ = v___x_3182_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v___y_3163_);
v_a_3206_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3179_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3179_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3214_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_inc_ref(v___y_3245_);
v___x_3250_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_3250_, 0, v___y_3245_);
lean_ctor_set(v___x_3250_, 1, v___y_3247_);
lean_ctor_set(v___x_3250_, 2, v___y_3231_);
lean_ctor_set(v___x_3250_, 3, v___y_3227_);
lean_ctor_set(v___x_3250_, 4, v___y_3226_);
lean_ctor_set(v___x_3250_, 5, v___y_3240_);
lean_ctor_set(v___x_3250_, 6, v___y_3224_);
lean_ctor_set(v___x_3250_, 7, v___y_3242_);
lean_ctor_set(v___x_3250_, 8, v___y_3229_);
lean_ctor_set(v___x_3250_, 9, v___y_3241_);
lean_ctor_set(v___x_3250_, 10, v___y_3221_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11, v___y_3225_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11 + 1, v___y_3217_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11 + 2, v___y_3215_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11 + 3, v___y_3239_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11 + 4, v___y_3249_);
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*11 + 5, v___y_3230_);
lean_inc_ref(v___y_3237_);
v___x_3251_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3237_, v___x_3250_, v___y_3222_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref(v___x_3251_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3235_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3234_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3238_);
lean_inc(v___y_3232_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3233_);
v___x_3252_ = l_Lean_Meta_Grind_propagateBeta(v___y_3233_, v___y_3246_, v___y_3222_, v___y_3232_, v___y_3238_, v___y_3223_, v___y_3234_, v___y_3220_, v___y_3244_, v___y_3216_, v___y_3235_, v___y_3218_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; 
lean_dec_ref(v___x_3252_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3235_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3234_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3238_);
lean_inc(v___y_3232_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3228_);
v___x_3253_ = l_Lean_Meta_Grind_propagateBeta(v___y_3228_, v___y_3236_, v___y_3222_, v___y_3232_, v___y_3238_, v___y_3223_, v___y_3234_, v___y_3220_, v___y_3244_, v___y_3216_, v___y_3235_, v___y_3218_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref(v___x_3253_);
v___x_3254_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3149_, v_lhsRoot_3148_, v___y_3222_, v___y_3244_, v___y_3216_, v___y_3235_, v___y_3218_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref(v___x_3254_);
v___x_3256_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3243_, v___y_3222_);
lean_dec_ref(v___y_3243_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v___x_3257_; 
lean_dec_ref(v___x_3256_);
lean_inc_ref(v___y_3237_);
lean_inc(v___y_3248_);
v___x_3257_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3248_, v___y_3237_, v___y_3222_, v___y_3232_, v___y_3238_, v___y_3223_, v___y_3234_, v___y_3220_, v___y_3244_, v___y_3216_, v___y_3235_, v___y_3218_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v___x_3258_; 
lean_dec_ref(v___x_3257_);
v___x_3258_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3222_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; uint8_t v___x_3260_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = lean_unbox(v_a_3259_);
lean_dec(v_a_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3245_, v___y_3222_, v___y_3232_, v___y_3238_, v___y_3223_, v___y_3234_, v___y_3220_, v___y_3244_, v___y_3216_, v___y_3235_, v___y_3218_);
lean_dec_ref(v___y_3245_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref(v___x_3261_);
v___y_3163_ = v___y_3228_;
v___y_3164_ = v___y_3237_;
v___y_3165_ = v___y_3219_;
v___y_3166_ = v___y_3233_;
v___y_3167_ = v_a_3255_;
v___y_3168_ = v___y_3248_;
v___y_3169_ = v___y_3222_;
v___y_3170_ = v___y_3232_;
v___y_3171_ = v___y_3238_;
v___y_3172_ = v___y_3223_;
v___y_3173_ = v___y_3234_;
v___y_3174_ = v___y_3220_;
v___y_3175_ = v___y_3244_;
v___y_3176_ = v___y_3216_;
v___y_3177_ = v___y_3235_;
v___y_3178_ = v___y_3218_;
goto v___jp_3162_;
}
else
{
lean_dec(v_a_3255_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
return v___x_3261_;
}
}
else
{
lean_dec_ref(v___y_3245_);
v___y_3163_ = v___y_3228_;
v___y_3164_ = v___y_3237_;
v___y_3165_ = v___y_3219_;
v___y_3166_ = v___y_3233_;
v___y_3167_ = v_a_3255_;
v___y_3168_ = v___y_3248_;
v___y_3169_ = v___y_3222_;
v___y_3170_ = v___y_3232_;
v___y_3171_ = v___y_3238_;
v___y_3172_ = v___y_3223_;
v___y_3173_ = v___y_3234_;
v___y_3174_ = v___y_3220_;
v___y_3175_ = v___y_3244_;
v___y_3176_ = v___y_3216_;
v___y_3177_ = v___y_3235_;
v___y_3178_ = v___y_3218_;
goto v___jp_3162_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_a_3255_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
v_a_3262_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3258_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3258_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_dec(v_a_3255_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
return v___x_3257_;
}
}
else
{
lean_dec(v_a_3255_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
return v___x_3256_;
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
v_a_3270_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3254_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3254_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
return v___x_3253_;
}
}
else
{
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
return v___x_3252_;
}
}
else
{
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
return v___x_3251_;
}
}
v___jp_3278_:
{
if (v_isHEq_3143_ == 0)
{
if (v___y_3304_ == 0)
{
v___y_3215_ = v___y_3279_;
v___y_3216_ = v___y_3281_;
v___y_3217_ = v___y_3280_;
v___y_3218_ = v___y_3282_;
v___y_3219_ = v___y_3283_;
v___y_3220_ = v___y_3284_;
v___y_3221_ = v___y_3285_;
v___y_3222_ = v___y_3287_;
v___y_3223_ = v___y_3286_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___y_3292_;
v___y_3226_ = v___y_3291_;
v___y_3227_ = v___y_3290_;
v___y_3228_ = v___y_3293_;
v___y_3229_ = v___y_3294_;
v___y_3230_ = v___y_3295_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3297_;
v___y_3233_ = v___y_3298_;
v___y_3234_ = v___y_3299_;
v___y_3235_ = v___y_3300_;
v___y_3236_ = v___y_3301_;
v___y_3237_ = v___y_3302_;
v___y_3238_ = v___y_3303_;
v___y_3239_ = v___y_3314_;
v___y_3240_ = v___y_3305_;
v___y_3241_ = v___y_3306_;
v___y_3242_ = v___y_3307_;
v___y_3243_ = v___y_3308_;
v___y_3244_ = v___y_3309_;
v___y_3245_ = v___y_3310_;
v___y_3246_ = v___y_3311_;
v___y_3247_ = v___y_3312_;
v___y_3248_ = v___y_3313_;
v___y_3249_ = v___y_3288_;
goto v___jp_3214_;
}
else
{
v___y_3215_ = v___y_3279_;
v___y_3216_ = v___y_3281_;
v___y_3217_ = v___y_3280_;
v___y_3218_ = v___y_3282_;
v___y_3219_ = v___y_3283_;
v___y_3220_ = v___y_3284_;
v___y_3221_ = v___y_3285_;
v___y_3222_ = v___y_3287_;
v___y_3223_ = v___y_3286_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___y_3292_;
v___y_3226_ = v___y_3291_;
v___y_3227_ = v___y_3290_;
v___y_3228_ = v___y_3293_;
v___y_3229_ = v___y_3294_;
v___y_3230_ = v___y_3295_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3297_;
v___y_3233_ = v___y_3298_;
v___y_3234_ = v___y_3299_;
v___y_3235_ = v___y_3300_;
v___y_3236_ = v___y_3301_;
v___y_3237_ = v___y_3302_;
v___y_3238_ = v___y_3303_;
v___y_3239_ = v___y_3314_;
v___y_3240_ = v___y_3305_;
v___y_3241_ = v___y_3306_;
v___y_3242_ = v___y_3307_;
v___y_3243_ = v___y_3308_;
v___y_3244_ = v___y_3309_;
v___y_3245_ = v___y_3310_;
v___y_3246_ = v___y_3311_;
v___y_3247_ = v___y_3312_;
v___y_3248_ = v___y_3313_;
v___y_3249_ = v___y_3304_;
goto v___jp_3214_;
}
}
else
{
v___y_3215_ = v___y_3279_;
v___y_3216_ = v___y_3281_;
v___y_3217_ = v___y_3280_;
v___y_3218_ = v___y_3282_;
v___y_3219_ = v___y_3283_;
v___y_3220_ = v___y_3284_;
v___y_3221_ = v___y_3285_;
v___y_3222_ = v___y_3287_;
v___y_3223_ = v___y_3286_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___y_3292_;
v___y_3226_ = v___y_3291_;
v___y_3227_ = v___y_3290_;
v___y_3228_ = v___y_3293_;
v___y_3229_ = v___y_3294_;
v___y_3230_ = v___y_3295_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3297_;
v___y_3233_ = v___y_3298_;
v___y_3234_ = v___y_3299_;
v___y_3235_ = v___y_3300_;
v___y_3236_ = v___y_3301_;
v___y_3237_ = v___y_3302_;
v___y_3238_ = v___y_3303_;
v___y_3239_ = v___y_3314_;
v___y_3240_ = v___y_3305_;
v___y_3241_ = v___y_3306_;
v___y_3242_ = v___y_3307_;
v___y_3243_ = v___y_3308_;
v___y_3244_ = v___y_3309_;
v___y_3245_ = v___y_3310_;
v___y_3246_ = v___y_3311_;
v___y_3247_ = v___y_3312_;
v___y_3248_ = v___y_3313_;
v___y_3249_ = v_isHEq_3143_;
goto v___jp_3214_;
}
}
v___jp_3315_:
{
lean_object* v___x_3338_; 
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
v___x_3338_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref(v___x_3338_);
v___x_3339_ = lean_st_ref_get(v___y_3328_);
v___x_3340_ = lean_st_ref_get(v___y_3328_);
lean_inc_ref(v___y_3318_);
v___x_3341_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3340_, v___y_3318_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v_self_3343_; lean_object* v_root_3344_; lean_object* v_congr_3345_; lean_object* v_target_x3f_3346_; lean_object* v_proof_x3f_3347_; uint8_t v_flipped_3348_; lean_object* v_size_3349_; uint8_t v_interpreted_3350_; uint8_t v_ctor_3351_; uint8_t v_hasLambdas_3352_; uint8_t v_heqProofs_3353_; lean_object* v_idx_3354_; lean_object* v_generation_3355_; lean_object* v_mt_3356_; lean_object* v_sTerms_3357_; uint8_t v_funCC_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3386_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref(v___x_3341_);
v_self_3343_ = lean_ctor_get(v_a_3342_, 0);
v_root_3344_ = lean_ctor_get(v_a_3342_, 2);
v_congr_3345_ = lean_ctor_get(v_a_3342_, 3);
v_target_x3f_3346_ = lean_ctor_get(v_a_3342_, 4);
v_proof_x3f_3347_ = lean_ctor_get(v_a_3342_, 5);
v_flipped_3348_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11);
v_size_3349_ = lean_ctor_get(v_a_3342_, 6);
v_interpreted_3350_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11 + 1);
v_ctor_3351_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11 + 2);
v_hasLambdas_3352_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11 + 3);
v_heqProofs_3353_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11 + 4);
v_idx_3354_ = lean_ctor_get(v_a_3342_, 7);
v_generation_3355_ = lean_ctor_get(v_a_3342_, 8);
v_mt_3356_ = lean_ctor_get(v_a_3342_, 9);
v_sTerms_3357_ = lean_ctor_get(v_a_3342_, 10);
v_funCC_3358_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*11 + 5);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_a_3342_, 1);
lean_dec(v_unused_3387_);
v___x_3360_ = v_a_3342_;
v_isShared_3361_ = v_isSharedCheck_3386_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_sTerms_3357_);
lean_inc(v_mt_3356_);
lean_inc(v_generation_3355_);
lean_inc(v_idx_3354_);
lean_inc(v_size_3349_);
lean_inc(v_proof_x3f_3347_);
lean_inc(v_target_x3f_3346_);
lean_inc(v_congr_3345_);
lean_inc(v_root_3344_);
lean_inc(v_self_3343_);
lean_dec(v_a_3342_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3386_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_self_3362_; lean_object* v_next_3363_; lean_object* v_root_3364_; lean_object* v_congr_3365_; lean_object* v_target_x3f_3366_; lean_object* v_proof_x3f_3367_; uint8_t v_flipped_3368_; lean_object* v_size_3369_; uint8_t v_interpreted_3370_; uint8_t v_ctor_3371_; uint8_t v_hasLambdas_3372_; uint8_t v_heqProofs_3373_; lean_object* v_idx_3374_; lean_object* v_generation_3375_; lean_object* v_mt_3376_; lean_object* v_sTerms_3377_; uint8_t v_funCC_3378_; lean_object* v___x_3380_; 
v_self_3362_ = lean_ctor_get(v_rhsRoot_3149_, 0);
v_next_3363_ = lean_ctor_get(v_rhsRoot_3149_, 1);
v_root_3364_ = lean_ctor_get(v_rhsRoot_3149_, 2);
v_congr_3365_ = lean_ctor_get(v_rhsRoot_3149_, 3);
v_target_x3f_3366_ = lean_ctor_get(v_rhsRoot_3149_, 4);
v_proof_x3f_3367_ = lean_ctor_get(v_rhsRoot_3149_, 5);
v_flipped_3368_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11);
v_size_3369_ = lean_ctor_get(v_rhsRoot_3149_, 6);
v_interpreted_3370_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11 + 1);
v_ctor_3371_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11 + 2);
v_hasLambdas_3372_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11 + 3);
v_heqProofs_3373_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11 + 4);
v_idx_3374_ = lean_ctor_get(v_rhsRoot_3149_, 7);
v_generation_3375_ = lean_ctor_get(v_rhsRoot_3149_, 8);
v_mt_3376_ = lean_ctor_get(v_rhsRoot_3149_, 9);
v_sTerms_3377_ = lean_ctor_get(v_rhsRoot_3149_, 10);
v_funCC_3378_ = lean_ctor_get_uint8(v_rhsRoot_3149_, sizeof(void*)*11 + 5);
lean_inc_ref(v_next_3363_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v_next_3363_);
v___x_3380_ = v___x_3360_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_self_3343_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_next_3363_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_root_3344_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_congr_3345_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_target_x3f_3346_);
lean_ctor_set(v_reuseFailAlloc_3385_, 5, v_proof_x3f_3347_);
lean_ctor_set(v_reuseFailAlloc_3385_, 6, v_size_3349_);
lean_ctor_set(v_reuseFailAlloc_3385_, 7, v_idx_3354_);
lean_ctor_set(v_reuseFailAlloc_3385_, 8, v_generation_3355_);
lean_ctor_set(v_reuseFailAlloc_3385_, 9, v_mt_3356_);
lean_ctor_set(v_reuseFailAlloc_3385_, 10, v_sTerms_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11, v_flipped_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11 + 1, v_interpreted_3350_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11 + 2, v_ctor_3351_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11 + 3, v_hasLambdas_3352_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11 + 4, v_heqProofs_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3385_, sizeof(void*)*11 + 5, v_funCC_3358_);
v___x_3380_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3325_, v___x_3380_, v___y_3328_);
if (lean_obj_tag(v___x_3381_) == 0)
{
uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v___x_3381_);
v___x_3382_ = 0;
v___x_3383_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3339_, v_lhs_3144_, v___x_3382_);
v___x_3384_ = lean_nat_add(v_size_3369_, v___y_3317_);
lean_dec(v___y_3317_);
if (v_hasLambdas_3372_ == 0)
{
lean_inc_ref(v_self_3362_);
lean_inc(v_idx_3374_);
lean_inc(v_mt_3376_);
lean_inc(v_proof_x3f_3367_);
lean_inc_ref(v_root_3364_);
lean_inc(v_generation_3375_);
lean_inc(v_target_x3f_3366_);
lean_inc_ref(v_congr_3365_);
lean_inc(v_sTerms_3377_);
v___y_3279_ = v_ctor_3371_;
v___y_3280_ = v_interpreted_3370_;
v___y_3281_ = v___y_3335_;
v___y_3282_ = v___y_3337_;
v___y_3283_ = v___x_3383_;
v___y_3284_ = v___y_3333_;
v___y_3285_ = v_sTerms_3377_;
v___y_3286_ = v___y_3331_;
v___y_3287_ = v___y_3328_;
v___y_3288_ = v___y_3324_;
v___y_3289_ = v___x_3384_;
v___y_3290_ = v_congr_3365_;
v___y_3291_ = v_target_x3f_3366_;
v___y_3292_ = v_flipped_3368_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v_generation_3375_;
v___y_3295_ = v_funCC_3378_;
v___y_3296_ = v_root_3364_;
v___y_3297_ = v___y_3329_;
v___y_3298_ = v___y_3323_;
v___y_3299_ = v___y_3332_;
v___y_3300_ = v___y_3336_;
v___y_3301_ = v___y_3319_;
v___y_3302_ = v___y_3320_;
v___y_3303_ = v___y_3330_;
v___y_3304_ = v_heqProofs_3373_;
v___y_3305_ = v_proof_x3f_3367_;
v___y_3306_ = v_mt_3376_;
v___y_3307_ = v_idx_3374_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___y_3334_;
v___y_3310_ = v_self_3362_;
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3327_;
v___y_3314_ = v___y_3326_;
goto v___jp_3278_;
}
else
{
lean_inc_ref(v_self_3362_);
lean_inc(v_idx_3374_);
lean_inc(v_mt_3376_);
lean_inc(v_proof_x3f_3367_);
lean_inc_ref(v_root_3364_);
lean_inc(v_generation_3375_);
lean_inc(v_target_x3f_3366_);
lean_inc_ref(v_congr_3365_);
lean_inc(v_sTerms_3377_);
v___y_3279_ = v_ctor_3371_;
v___y_3280_ = v_interpreted_3370_;
v___y_3281_ = v___y_3335_;
v___y_3282_ = v___y_3337_;
v___y_3283_ = v___x_3383_;
v___y_3284_ = v___y_3333_;
v___y_3285_ = v_sTerms_3377_;
v___y_3286_ = v___y_3331_;
v___y_3287_ = v___y_3328_;
v___y_3288_ = v___y_3324_;
v___y_3289_ = v___x_3384_;
v___y_3290_ = v_congr_3365_;
v___y_3291_ = v_target_x3f_3366_;
v___y_3292_ = v_flipped_3368_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v_generation_3375_;
v___y_3295_ = v_funCC_3378_;
v___y_3296_ = v_root_3364_;
v___y_3297_ = v___y_3329_;
v___y_3298_ = v___y_3323_;
v___y_3299_ = v___y_3332_;
v___y_3300_ = v___y_3336_;
v___y_3301_ = v___y_3319_;
v___y_3302_ = v___y_3320_;
v___y_3303_ = v___y_3330_;
v___y_3304_ = v_heqProofs_3373_;
v___y_3305_ = v_proof_x3f_3367_;
v___y_3306_ = v_mt_3376_;
v___y_3307_ = v_idx_3374_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___y_3334_;
v___y_3310_ = v_self_3362_;
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3327_;
v___y_3314_ = v_hasLambdas_3372_;
goto v___jp_3278_;
}
}
else
{
lean_dec(v___x_3339_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v___x_3339_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
v_a_3388_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3341_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3341_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
return v___x_3338_;
}
}
v___jp_3397_:
{
lean_object* v_self_3413_; lean_object* v_next_3414_; lean_object* v_size_3415_; uint8_t v_hasLambdas_3416_; uint8_t v_heqProofs_3417_; lean_object* v___x_3418_; 
v_self_3413_ = lean_ctor_get(v_lhsRoot_3148_, 0);
v_next_3414_ = lean_ctor_get(v_lhsRoot_3148_, 1);
v_size_3415_ = lean_ctor_get(v_lhsRoot_3148_, 6);
v_hasLambdas_3416_ = lean_ctor_get_uint8(v_lhsRoot_3148_, sizeof(void*)*11 + 3);
v_heqProofs_3417_ = lean_ctor_get_uint8(v_lhsRoot_3148_, sizeof(void*)*11 + 4);
v___x_3418_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3413_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v_root_3420_; lean_object* v___x_3421_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
v_root_3420_ = lean_ctor_get(v_rhsNode_3147_, 2);
lean_inc_ref(v_root_3420_);
lean_dec_ref(v_rhsNode_3147_);
lean_inc_ref(v_root_3420_);
lean_inc_ref(v_lhs_3144_);
v___x_3421_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3144_, v_root_3420_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; lean_object* v_a_3423_; uint8_t v___x_3424_; 
lean_dec_ref(v___x_3421_);
v___x_3422_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3396_, v___y_3411_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = lean_unbox(v_a_3423_);
lean_dec(v_a_3423_);
if (v___x_3424_ == 0)
{
lean_inc_ref(v_next_3414_);
lean_inc_ref(v_self_3413_);
lean_inc(v_size_3415_);
v___y_3316_ = v___y_3398_;
v___y_3317_ = v_size_3415_;
v___y_3318_ = v_self_3413_;
v___y_3319_ = v_fns_u2082_3402_;
v___y_3320_ = v_root_3420_;
v___y_3321_ = v___y_3399_;
v___y_3322_ = v_next_3414_;
v___y_3323_ = v___y_3400_;
v___y_3324_ = v_heqProofs_3417_;
v___y_3325_ = v___y_3401_;
v___y_3326_ = v_hasLambdas_3416_;
v___y_3327_ = v_a_3419_;
v___y_3328_ = v___y_3403_;
v___y_3329_ = v___y_3404_;
v___y_3330_ = v___y_3405_;
v___y_3331_ = v___y_3406_;
v___y_3332_ = v___y_3407_;
v___y_3333_ = v___y_3408_;
v___y_3334_ = v___y_3409_;
v___y_3335_ = v___y_3410_;
v___y_3336_ = v___y_3411_;
v___y_3337_ = v___y_3412_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Meta_Grind_updateLastTag(v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3426_; 
lean_dec_ref(v___x_3425_);
lean_inc(v___y_3412_);
lean_inc_ref(v___y_3411_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc_ref(v_lhs_3144_);
v___x_3426_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3144_, v___y_3403_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
lean_inc(v___y_3412_);
lean_inc_ref(v___y_3411_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc_ref(v_root_3420_);
v___x_3428_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3420_, v___y_3403_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = lean_st_ref_get(v___y_3403_);
lean_inc_ref(v_lhs_3144_);
v___x_3431_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3430_, v_lhs_3144_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref(v___x_3431_);
lean_inc(v___y_3412_);
lean_inc_ref(v___y_3411_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
v___x_3433_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3432_, v___y_3403_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref(v___x_3433_);
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_a_3427_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_a_3429_);
v___x_3438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v_a_3434_);
v___x_3441_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_cls_3396_, v___x_3440_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_dec_ref(v___x_3441_);
lean_inc_ref(v_next_3414_);
lean_inc_ref(v_self_3413_);
lean_inc(v_size_3415_);
v___y_3316_ = v___y_3398_;
v___y_3317_ = v_size_3415_;
v___y_3318_ = v_self_3413_;
v___y_3319_ = v_fns_u2082_3402_;
v___y_3320_ = v_root_3420_;
v___y_3321_ = v___y_3399_;
v___y_3322_ = v_next_3414_;
v___y_3323_ = v___y_3400_;
v___y_3324_ = v_heqProofs_3417_;
v___y_3325_ = v___y_3401_;
v___y_3326_ = v_hasLambdas_3416_;
v___y_3327_ = v_a_3419_;
v___y_3328_ = v___y_3403_;
v___y_3329_ = v___y_3404_;
v___y_3330_ = v___y_3405_;
v___y_3331_ = v___y_3406_;
v___y_3332_ = v___y_3407_;
v___y_3333_ = v___y_3408_;
v___y_3334_ = v___y_3409_;
v___y_3335_ = v___y_3410_;
v___y_3336_ = v___y_3411_;
v___y_3337_ = v___y_3412_;
goto v___jp_3315_;
}
else
{
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
return v___x_3441_;
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v_a_3429_);
lean_dec(v_a_3427_);
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
v_a_3442_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3433_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3433_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v_a_3429_);
lean_dec(v_a_3427_);
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
v_a_3450_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3431_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3431_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v_a_3427_);
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
v_a_3458_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3428_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3428_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
v_a_3466_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3426_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3426_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
return v___x_3425_;
}
}
}
else
{
lean_dec_ref(v_root_3420_);
lean_dec(v_a_3419_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_lhs_3144_);
return v___x_3421_;
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_fns_u2082_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
v_a_3474_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3418_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3418_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
v___jp_3482_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3497_ = lean_array_get_size(v___y_3483_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = lean_nat_dec_eq(v___x_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v_self_3500_; lean_object* v___x_3501_; 
v_self_3500_ = lean_ctor_get(v_lhsRoot_3148_, 0);
lean_inc(v___y_3496_);
lean_inc_ref(v___y_3495_);
lean_inc(v___y_3494_);
lean_inc_ref(v___y_3493_);
lean_inc(v___y_3492_);
lean_inc_ref(v___y_3491_);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
lean_inc(v___y_3488_);
lean_inc(v___y_3487_);
lean_inc_ref(v_self_3500_);
v___x_3501_ = l_Lean_Meta_Grind_getFnRoots(v_self_3500_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
v___y_3398_ = v___y_3483_;
v___y_3399_ = v_fns_u2081_3486_;
v___y_3400_ = v___y_3484_;
v___y_3401_ = v___y_3485_;
v_fns_u2082_3402_ = v_a_3502_;
v___y_3403_ = v___y_3487_;
v___y_3404_ = v___y_3488_;
v___y_3405_ = v___y_3489_;
v___y_3406_ = v___y_3490_;
v___y_3407_ = v___y_3491_;
v___y_3408_ = v___y_3492_;
v___y_3409_ = v___y_3493_;
v___y_3410_ = v___y_3494_;
v___y_3411_ = v___y_3495_;
v___y_3412_ = v___y_3496_;
goto v___jp_3397_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v_fns_u2081_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
v_a_3503_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3501_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
v___y_3398_ = v___y_3483_;
v___y_3399_ = v_fns_u2081_3486_;
v___y_3400_ = v___y_3484_;
v___y_3401_ = v___y_3485_;
v_fns_u2082_3402_ = v___x_3511_;
v___y_3403_ = v___y_3487_;
v___y_3404_ = v___y_3488_;
v___y_3405_ = v___y_3489_;
v___y_3406_ = v___y_3490_;
v___y_3407_ = v___y_3491_;
v___y_3408_ = v___y_3492_;
v___y_3409_ = v___y_3493_;
v___y_3410_ = v___y_3494_;
v___y_3411_ = v___y_3495_;
v___y_3412_ = v___y_3496_;
goto v___jp_3397_;
}
}
v___jp_3512_:
{
lean_object* v___x_3523_; 
lean_inc_ref(v_lhs_3144_);
v___x_3523_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3144_, v___y_3513_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3590_; 
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3591_);
v___x_3525_ = v___x_3523_;
v_isShared_3526_ = v_isSharedCheck_3590_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v___x_3523_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3590_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_self_3527_; lean_object* v_next_3528_; lean_object* v_root_3529_; lean_object* v_congr_3530_; lean_object* v_size_3531_; uint8_t v_interpreted_3532_; uint8_t v_ctor_3533_; uint8_t v_hasLambdas_3534_; uint8_t v_heqProofs_3535_; lean_object* v_idx_3536_; lean_object* v_generation_3537_; lean_object* v_mt_3538_; lean_object* v_sTerms_3539_; uint8_t v_funCC_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3587_; 
v_self_3527_ = lean_ctor_get(v_lhsNode_3146_, 0);
v_next_3528_ = lean_ctor_get(v_lhsNode_3146_, 1);
v_root_3529_ = lean_ctor_get(v_lhsNode_3146_, 2);
v_congr_3530_ = lean_ctor_get(v_lhsNode_3146_, 3);
v_size_3531_ = lean_ctor_get(v_lhsNode_3146_, 6);
v_interpreted_3532_ = lean_ctor_get_uint8(v_lhsNode_3146_, sizeof(void*)*11 + 1);
v_ctor_3533_ = lean_ctor_get_uint8(v_lhsNode_3146_, sizeof(void*)*11 + 2);
v_hasLambdas_3534_ = lean_ctor_get_uint8(v_lhsNode_3146_, sizeof(void*)*11 + 3);
v_heqProofs_3535_ = lean_ctor_get_uint8(v_lhsNode_3146_, sizeof(void*)*11 + 4);
v_idx_3536_ = lean_ctor_get(v_lhsNode_3146_, 7);
v_generation_3537_ = lean_ctor_get(v_lhsNode_3146_, 8);
v_mt_3538_ = lean_ctor_get(v_lhsNode_3146_, 9);
v_sTerms_3539_ = lean_ctor_get(v_lhsNode_3146_, 10);
v_funCC_3540_ = lean_ctor_get_uint8(v_lhsNode_3146_, sizeof(void*)*11 + 5);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_lhsNode_3146_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; lean_object* v_unused_3589_; 
v_unused_3588_ = lean_ctor_get(v_lhsNode_3146_, 5);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_lhsNode_3146_, 4);
lean_dec(v_unused_3589_);
v___x_3542_ = v_lhsNode_3146_;
v_isShared_3543_ = v_isSharedCheck_3587_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_sTerms_3539_);
lean_inc(v_mt_3538_);
lean_inc(v_generation_3537_);
lean_inc(v_idx_3536_);
lean_inc(v_size_3531_);
lean_inc(v_congr_3530_);
lean_inc(v_root_3529_);
lean_inc(v_next_3528_);
lean_inc(v_self_3527_);
lean_dec(v_lhsNode_3146_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3587_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 1);
lean_ctor_set(v___x_3525_, 0, v_rhs_3145_);
v___x_3545_ = v___x_3525_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_rhs_3145_);
v___x_3545_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_proof_3142_);
lean_inc_ref(v_root_3529_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 5, v___x_3546_);
lean_ctor_set(v___x_3542_, 4, v___x_3545_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_self_3527_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_next_3528_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_root_3529_);
lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_congr_3530_);
lean_ctor_set(v_reuseFailAlloc_3585_, 4, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3585_, 5, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3585_, 6, v_size_3531_);
lean_ctor_set(v_reuseFailAlloc_3585_, 7, v_idx_3536_);
lean_ctor_set(v_reuseFailAlloc_3585_, 8, v_generation_3537_);
lean_ctor_set(v_reuseFailAlloc_3585_, 9, v_mt_3538_);
lean_ctor_set(v_reuseFailAlloc_3585_, 10, v_sTerms_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*11 + 1, v_interpreted_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*11 + 2, v_ctor_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*11 + 3, v_hasLambdas_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*11 + 4, v_heqProofs_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*11 + 5, v_funCC_3540_);
v___x_3548_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3549_; 
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*11, v_flipped_3150_);
lean_inc_ref(v_lhs_3144_);
v___x_3549_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3144_, v___x_3548_, v___y_3513_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3550_; 
lean_dec_ref(v___x_3549_);
lean_inc(v___y_3522_);
lean_inc_ref(v___y_3521_);
lean_inc(v___y_3520_);
lean_inc_ref(v___y_3519_);
lean_inc(v___y_3518_);
lean_inc_ref(v___y_3517_);
lean_inc(v___y_3516_);
lean_inc_ref(v___y_3515_);
lean_inc(v___y_3514_);
lean_inc(v___y_3513_);
v___x_3550_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3148_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref(v___x_3550_);
lean_inc(v___y_3522_);
lean_inc_ref(v___y_3521_);
lean_inc(v___y_3520_);
lean_inc_ref(v___y_3519_);
lean_inc(v___y_3518_);
lean_inc_ref(v___y_3517_);
lean_inc(v___y_3516_);
lean_inc_ref(v___y_3515_);
lean_inc(v___y_3514_);
lean_inc(v___y_3513_);
v___x_3552_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3149_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = lean_array_get_size(v_a_3551_);
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = lean_nat_dec_eq(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v_self_3557_; lean_object* v___x_3558_; 
v_self_3557_ = lean_ctor_get(v_rhsRoot_3149_, 0);
lean_inc(v___y_3522_);
lean_inc_ref(v___y_3521_);
lean_inc(v___y_3520_);
lean_inc_ref(v___y_3519_);
lean_inc(v___y_3518_);
lean_inc_ref(v___y_3517_);
lean_inc(v___y_3516_);
lean_inc_ref(v___y_3515_);
lean_inc(v___y_3514_);
lean_inc(v___y_3513_);
lean_inc_ref(v_self_3557_);
v___x_3558_ = l_Lean_Meta_Grind_getFnRoots(v_self_3557_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
v___y_3483_ = v_a_3553_;
v___y_3484_ = v_a_3551_;
v___y_3485_ = v_root_3529_;
v_fns_u2081_3486_ = v_a_3559_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
v___y_3494_ = v___y_3520_;
v___y_3495_ = v___y_3521_;
v___y_3496_ = v___y_3522_;
goto v___jp_3482_;
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_a_3553_);
lean_dec(v_a_3551_);
lean_dec_ref(v_root_3529_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
v_a_3560_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3558_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3558_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v___x_3568_; 
v___x_3568_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___closed__0));
v___y_3483_ = v_a_3553_;
v___y_3484_ = v_a_3551_;
v___y_3485_ = v_root_3529_;
v_fns_u2081_3486_ = v___x_3568_;
v___y_3487_ = v___y_3513_;
v___y_3488_ = v___y_3514_;
v___y_3489_ = v___y_3515_;
v___y_3490_ = v___y_3516_;
v___y_3491_ = v___y_3517_;
v___y_3492_ = v___y_3518_;
v___y_3493_ = v___y_3519_;
v___y_3494_ = v___y_3520_;
v___y_3495_ = v___y_3521_;
v___y_3496_ = v___y_3522_;
goto v___jp_3482_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_a_3551_);
lean_dec_ref(v_root_3529_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
v_a_3569_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3552_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3552_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v_root_3529_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
v_a_3577_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3550_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3550_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_dec_ref(v_root_3529_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhs_3144_);
return v___x_3549_;
}
}
}
}
}
}
else
{
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3149_);
lean_dec_ref(v_lhsRoot_3148_);
lean_dec_ref(v_rhsNode_3147_);
lean_dec_ref(v_lhsNode_3146_);
lean_dec_ref(v_rhs_3145_);
lean_dec_ref(v_lhs_3144_);
lean_dec_ref(v_proof_3142_);
return v___x_3523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3622_ = _args[0];
lean_object* v_isHEq_3623_ = _args[1];
lean_object* v_lhs_3624_ = _args[2];
lean_object* v_rhs_3625_ = _args[3];
lean_object* v_lhsNode_3626_ = _args[4];
lean_object* v_rhsNode_3627_ = _args[5];
lean_object* v_lhsRoot_3628_ = _args[6];
lean_object* v_rhsRoot_3629_ = _args[7];
lean_object* v_flipped_3630_ = _args[8];
lean_object* v_a_3631_ = _args[9];
lean_object* v_a_3632_ = _args[10];
lean_object* v_a_3633_ = _args[11];
lean_object* v_a_3634_ = _args[12];
lean_object* v_a_3635_ = _args[13];
lean_object* v_a_3636_ = _args[14];
lean_object* v_a_3637_ = _args[15];
lean_object* v_a_3638_ = _args[16];
lean_object* v_a_3639_ = _args[17];
lean_object* v_a_3640_ = _args[18];
lean_object* v_a_3641_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3642_; uint8_t v_flipped_boxed_3643_; lean_object* v_res_3644_; 
v_isHEq_boxed_3642_ = lean_unbox(v_isHEq_3623_);
v_flipped_boxed_3643_ = lean_unbox(v_flipped_3630_);
v_res_3644_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3622_, v_isHEq_boxed_3642_, v_lhs_3624_, v_rhs_3625_, v_lhsNode_3626_, v_rhsNode_3627_, v_lhsRoot_3628_, v_rhsRoot_3629_, v_flipped_boxed_3643_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3645_, lean_object* v_as_x27_3646_, lean_object* v_b_3647_, lean_object* v_a_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3646_, v_b_3647_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3661_, lean_object* v_as_x27_3662_, lean_object* v_b_3663_, lean_object* v_a_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3661_, v_as_x27_3662_, v_b_3663_, v_a_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v_as_3661_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3677_, lean_object* v_as_x27_3678_, lean_object* v_b_3679_, lean_object* v_a_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3678_, v_b_3679_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3693_, lean_object* v_as_x27_3694_, lean_object* v_b_3695_, lean_object* v_a_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3693_, v_as_x27_3694_, v_b_3695_, v_a_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v_as_3693_);
return v_res_3708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_3722_, lean_object* v_rhs_3723_, lean_object* v_proof_3724_, uint8_t v_isHEq_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_st_ref_get(v_a_3726_);
lean_inc_ref(v_lhs_3722_);
v___x_3741_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3740_, v_lhs_3722_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref(v___x_3741_);
v___x_3743_ = lean_st_ref_get(v_a_3726_);
lean_inc_ref(v_rhs_3723_);
v___x_3744_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3743_, v_rhs_3723_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v_root_3746_; lean_object* v_root_3747_; uint8_t v___x_3748_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3744_);
v_root_3746_ = lean_ctor_get(v_a_3742_, 2);
v_root_3747_ = lean_ctor_get(v_a_3745_, 2);
v___x_3748_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_3746_, v_root_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; uint8_t v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; uint8_t v___y_3823_; lean_object* v___y_3828_; uint8_t v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; uint8_t v___y_3855_; lean_object* v___y_3856_; uint8_t v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3871_; uint8_t v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; uint8_t v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_a_3888_; uint8_t v___x_3889_; lean_object* v___y_3891_; uint8_t v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; uint8_t v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3907_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; uint8_t v___y_3921_; lean_object* v___y_3923_; uint8_t v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v_size_3934_; uint8_t v_interpreted_3935_; uint8_t v_ctor_3936_; uint8_t v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v_size_3940_; lean_object* v___y_3943_; uint8_t v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; uint8_t v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; uint8_t v___y_3957_; lean_object* v___y_3968_; lean_object* v___y_3969_; uint8_t v_interpreted_3970_; uint8_t v_valueInconsistency_3971_; uint8_t v_trueEqFalse_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3985_; lean_object* v___y_3986_; uint8_t v_valueInconsistency_3987_; uint8_t v_trueEqFalse_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; uint8_t v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4098_; uint8_t v___x_4110_; 
v___x_3886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_3887_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_3886_, v_a_3734_);
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref(v___x_3887_);
v___x_3889_ = 1;
v___x_4110_ = lean_unbox(v_a_3888_);
lean_dec(v_a_3888_);
if (v___x_4110_ == 0)
{
v___y_4062_ = v_a_3726_;
v___y_4063_ = v_a_3727_;
v___y_4064_ = v_a_3728_;
v___y_4065_ = v_a_3729_;
v___y_4066_ = v_a_3730_;
v___y_4067_ = v_a_3731_;
v___y_4068_ = v_a_3732_;
v___y_4069_ = v_a_3733_;
v___y_4070_ = v_a_3734_;
v___y_4071_ = v_a_3735_;
goto v___jp_4061_;
}
else
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Meta_Grind_updateLastTag(v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_dec_ref(v___x_4111_);
if (v_isHEq_3725_ == 0)
{
lean_object* v___x_4112_; 
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
lean_inc_ref(v_rhs_3723_);
lean_inc_ref(v_lhs_3722_);
v___x_4112_ = l_Lean_Meta_mkEq(v_lhs_3722_, v_rhs_3723_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_4098_ = v___x_4112_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4113_; 
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
lean_inc_ref(v_rhs_3723_);
lean_inc_ref(v_lhs_3722_);
v___x_4113_ = l_Lean_Meta_mkHEq(v_lhs_3722_, v_rhs_3723_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_4098_ = v___x_4113_;
goto v___jp_4097_;
}
}
else
{
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
return v___x_4111_;
}
}
v___jp_3749_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v_a_3762_; uint8_t v___x_3763_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3761_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_3760_, v___y_3758_);
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = lean_unbox(v_a_3762_);
lean_dec(v_a_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_Grind_checkInvariants(v___x_3748_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3764_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Meta_Grind_updateLastTag(v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_dec_ref(v___x_3765_);
v___x_3766_ = lean_st_ref_get(v___y_3750_);
lean_inc(v___y_3759_);
lean_inc_ref(v___y_3758_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
v___x_3767_ = l_Lean_Meta_Grind_Goal_ppState(v___x_3766_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v_a_3768_);
v___x_3771_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_3760_, v___x_3770_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3772_; 
lean_dec_ref(v___x_3771_);
v___x_3772_ = l_Lean_Meta_Grind_checkInvariants(v___x_3748_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3772_;
}
else
{
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec(v___y_3750_);
return v___x_3771_;
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec(v___y_3750_);
v_a_3773_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3767_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3767_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec(v___y_3750_);
return v___x_3765_;
}
}
}
v___jp_3781_:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3785_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; uint8_t v___x_3797_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = lean_unbox(v_a_3796_);
lean_dec(v_a_3796_);
if (v___x_3797_ == 0)
{
if (v___y_3783_ == 0)
{
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3782_);
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
goto v___jp_3749_;
}
else
{
lean_object* v_self_3798_; lean_object* v_self_3799_; lean_object* v___x_3800_; 
v_self_3798_ = lean_ctor_get(v___y_3784_, 0);
lean_inc_ref(v_self_3798_);
lean_dec_ref(v___y_3784_);
v_self_3799_ = lean_ctor_get(v___y_3782_, 0);
lean_inc_ref(v_self_3799_);
lean_dec_ref(v___y_3782_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v___y_3786_);
lean_inc(v___y_3785_);
v___x_3800_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_3798_, v_self_3799_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref(v___x_3800_);
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
goto v___jp_3749_;
}
else
{
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
return v___x_3800_;
}
}
}
else
{
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3782_);
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
goto v___jp_3749_;
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3782_);
v_a_3801_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3795_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3795_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
v___jp_3809_:
{
if (v___y_3823_ == 0)
{
v___y_3782_ = v___y_3819_;
v___y_3783_ = v___y_3820_;
v___y_3784_ = v___y_3821_;
v___y_3785_ = v___y_3813_;
v___y_3786_ = v___y_3811_;
v___y_3787_ = v___y_3816_;
v___y_3788_ = v___y_3822_;
v___y_3789_ = v___y_3812_;
v___y_3790_ = v___y_3817_;
v___y_3791_ = v___y_3814_;
v___y_3792_ = v___y_3810_;
v___y_3793_ = v___y_3818_;
v___y_3794_ = v___y_3815_;
goto v___jp_3781_;
}
else
{
lean_object* v_self_3824_; lean_object* v_self_3825_; lean_object* v___x_3826_; 
v_self_3824_ = lean_ctor_get(v___y_3821_, 0);
v_self_3825_ = lean_ctor_get(v___y_3819_, 0);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3810_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3812_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3811_);
lean_inc(v___y_3813_);
lean_inc_ref(v_self_3825_);
lean_inc_ref(v_self_3824_);
v___x_3826_ = l_Lean_Meta_Grind_propagateCtor(v_self_3824_, v_self_3825_, v___y_3813_, v___y_3811_, v___y_3816_, v___y_3822_, v___y_3812_, v___y_3817_, v___y_3814_, v___y_3810_, v___y_3818_, v___y_3815_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_dec_ref(v___x_3826_);
v___y_3782_ = v___y_3819_;
v___y_3783_ = v___y_3820_;
v___y_3784_ = v___y_3821_;
v___y_3785_ = v___y_3813_;
v___y_3786_ = v___y_3811_;
v___y_3787_ = v___y_3816_;
v___y_3788_ = v___y_3822_;
v___y_3789_ = v___y_3812_;
v___y_3790_ = v___y_3817_;
v___y_3791_ = v___y_3814_;
v___y_3792_ = v___y_3810_;
v___y_3793_ = v___y_3818_;
v___y_3794_ = v___y_3815_;
goto v___jp_3781_;
}
else
{
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec(v___y_3810_);
return v___x_3826_;
}
}
}
v___jp_3827_:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3831_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; uint8_t v___x_3843_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v___x_3841_);
v___x_3843_ = lean_unbox(v_a_3842_);
lean_dec(v_a_3842_);
if (v___x_3843_ == 0)
{
uint8_t v_ctor_3844_; 
v_ctor_3844_ = lean_ctor_get_uint8(v___y_3830_, sizeof(void*)*11 + 2);
if (v_ctor_3844_ == 0)
{
v___y_3810_ = v___y_3838_;
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3835_;
v___y_3813_ = v___y_3831_;
v___y_3814_ = v___y_3837_;
v___y_3815_ = v___y_3840_;
v___y_3816_ = v___y_3833_;
v___y_3817_ = v___y_3836_;
v___y_3818_ = v___y_3839_;
v___y_3819_ = v___y_3828_;
v___y_3820_ = v___y_3829_;
v___y_3821_ = v___y_3830_;
v___y_3822_ = v___y_3834_;
v___y_3823_ = v___x_3748_;
goto v___jp_3809_;
}
else
{
uint8_t v_ctor_3845_; 
v_ctor_3845_ = lean_ctor_get_uint8(v___y_3828_, sizeof(void*)*11 + 2);
v___y_3810_ = v___y_3838_;
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3835_;
v___y_3813_ = v___y_3831_;
v___y_3814_ = v___y_3837_;
v___y_3815_ = v___y_3840_;
v___y_3816_ = v___y_3833_;
v___y_3817_ = v___y_3836_;
v___y_3818_ = v___y_3839_;
v___y_3819_ = v___y_3828_;
v___y_3820_ = v___y_3829_;
v___y_3821_ = v___y_3830_;
v___y_3822_ = v___y_3834_;
v___y_3823_ = v_ctor_3845_;
goto v___jp_3809_;
}
}
else
{
v___y_3782_ = v___y_3828_;
v___y_3783_ = v___y_3829_;
v___y_3784_ = v___y_3830_;
v___y_3785_ = v___y_3831_;
v___y_3786_ = v___y_3832_;
v___y_3787_ = v___y_3833_;
v___y_3788_ = v___y_3834_;
v___y_3789_ = v___y_3835_;
v___y_3790_ = v___y_3836_;
v___y_3791_ = v___y_3837_;
v___y_3792_ = v___y_3838_;
v___y_3793_ = v___y_3839_;
v___y_3794_ = v___y_3840_;
goto v___jp_3781_;
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3828_);
v_a_3846_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3841_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3841_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
v___jp_3854_:
{
if (v___y_3855_ == 0)
{
v___y_3828_ = v___y_3856_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___y_3858_;
v___y_3831_ = v___y_3859_;
v___y_3832_ = v___y_3860_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___y_3866_;
v___y_3839_ = v___y_3867_;
v___y_3840_ = v___y_3868_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3869_; 
lean_inc(v___y_3868_);
lean_inc_ref(v___y_3867_);
lean_inc(v___y_3866_);
lean_inc_ref(v___y_3865_);
lean_inc(v___y_3864_);
lean_inc_ref(v___y_3863_);
lean_inc(v___y_3862_);
lean_inc_ref(v___y_3861_);
lean_inc(v___y_3860_);
lean_inc(v___y_3859_);
v___x_3869_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_dec_ref(v___x_3869_);
v___y_3828_ = v___y_3856_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___y_3858_;
v___y_3831_ = v___y_3859_;
v___y_3832_ = v___y_3860_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___y_3866_;
v___y_3839_ = v___y_3867_;
v___y_3840_ = v___y_3868_;
goto v___jp_3827_;
}
else
{
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v___y_3856_);
return v___x_3869_;
}
}
}
v___jp_3870_:
{
lean_object* v___x_3885_; 
lean_inc(v___y_3884_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3879_);
lean_inc_ref(v___y_3875_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3874_);
lean_inc(v___y_3880_);
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3881_);
lean_inc_ref(v___y_3883_);
v___x_3885_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3724_, v_isHEq_3725_, v_lhs_3722_, v_rhs_3723_, v_a_3742_, v_a_3745_, v___y_3883_, v___y_3881_, v___x_3748_, v___y_3871_, v___y_3880_, v___y_3874_, v___y_3878_, v___y_3875_, v___y_3879_, v___y_3873_, v___y_3876_, v___y_3877_, v___y_3884_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_dec_ref(v___x_3885_);
v___y_3855_ = v___y_3872_;
v___y_3856_ = v___y_3881_;
v___y_3857_ = v___y_3882_;
v___y_3858_ = v___y_3883_;
v___y_3859_ = v___y_3871_;
v___y_3860_ = v___y_3880_;
v___y_3861_ = v___y_3874_;
v___y_3862_ = v___y_3878_;
v___y_3863_ = v___y_3875_;
v___y_3864_ = v___y_3879_;
v___y_3865_ = v___y_3873_;
v___y_3866_ = v___y_3876_;
v___y_3867_ = v___y_3877_;
v___y_3868_ = v___y_3884_;
goto v___jp_3854_;
}
else
{
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3871_);
return v___x_3885_;
}
}
v___jp_3890_:
{
lean_object* v___x_3905_; 
lean_inc(v___y_3904_);
lean_inc_ref(v___y_3897_);
lean_inc(v___y_3896_);
lean_inc_ref(v___y_3893_);
lean_inc(v___y_3899_);
lean_inc_ref(v___y_3895_);
lean_inc(v___y_3898_);
lean_inc_ref(v___y_3894_);
lean_inc(v___y_3900_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3903_);
lean_inc_ref(v___y_3901_);
v___x_3905_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3724_, v_isHEq_3725_, v_rhs_3723_, v_lhs_3722_, v_a_3745_, v_a_3742_, v___y_3901_, v___y_3903_, v___x_3889_, v___y_3891_, v___y_3900_, v___y_3894_, v___y_3898_, v___y_3895_, v___y_3899_, v___y_3893_, v___y_3896_, v___y_3897_, v___y_3904_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_dec_ref(v___x_3905_);
v___y_3855_ = v___y_3892_;
v___y_3856_ = v___y_3901_;
v___y_3857_ = v___y_3902_;
v___y_3858_ = v___y_3903_;
v___y_3859_ = v___y_3891_;
v___y_3860_ = v___y_3900_;
v___y_3861_ = v___y_3894_;
v___y_3862_ = v___y_3898_;
v___y_3863_ = v___y_3895_;
v___y_3864_ = v___y_3899_;
v___y_3865_ = v___y_3893_;
v___y_3866_ = v___y_3896_;
v___y_3867_ = v___y_3897_;
v___y_3868_ = v___y_3904_;
goto v___jp_3854_;
}
else
{
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
return v___x_3905_;
}
}
v___jp_3906_:
{
if (v___y_3921_ == 0)
{
v___y_3871_ = v___y_3907_;
v___y_3872_ = v___y_3908_;
v___y_3873_ = v___y_3909_;
v___y_3874_ = v___y_3910_;
v___y_3875_ = v___y_3911_;
v___y_3876_ = v___y_3912_;
v___y_3877_ = v___y_3913_;
v___y_3878_ = v___y_3914_;
v___y_3879_ = v___y_3915_;
v___y_3880_ = v___y_3916_;
v___y_3881_ = v___y_3917_;
v___y_3882_ = v___y_3918_;
v___y_3883_ = v___y_3920_;
v___y_3884_ = v___y_3919_;
goto v___jp_3870_;
}
else
{
v___y_3891_ = v___y_3907_;
v___y_3892_ = v___y_3908_;
v___y_3893_ = v___y_3909_;
v___y_3894_ = v___y_3910_;
v___y_3895_ = v___y_3911_;
v___y_3896_ = v___y_3912_;
v___y_3897_ = v___y_3913_;
v___y_3898_ = v___y_3914_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___y_3916_;
v___y_3901_ = v___y_3917_;
v___y_3902_ = v___y_3918_;
v___y_3903_ = v___y_3920_;
v___y_3904_ = v___y_3919_;
goto v___jp_3890_;
}
}
v___jp_3922_:
{
uint8_t v___x_3941_; 
v___x_3941_ = lean_nat_dec_lt(v_size_3934_, v_size_3940_);
lean_dec(v_size_3940_);
lean_dec(v_size_3934_);
if (v___x_3941_ == 0)
{
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
v___y_3910_ = v___y_3926_;
v___y_3911_ = v___y_3927_;
v___y_3912_ = v___y_3928_;
v___y_3913_ = v___y_3929_;
v___y_3914_ = v___y_3930_;
v___y_3915_ = v___y_3931_;
v___y_3916_ = v___y_3932_;
v___y_3917_ = v___y_3933_;
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3938_;
v___y_3920_ = v___y_3939_;
v___y_3921_ = v___x_3748_;
goto v___jp_3906_;
}
else
{
if (v_interpreted_3935_ == 0)
{
if (v___x_3941_ == 0)
{
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
v___y_3910_ = v___y_3926_;
v___y_3911_ = v___y_3927_;
v___y_3912_ = v___y_3928_;
v___y_3913_ = v___y_3929_;
v___y_3914_ = v___y_3930_;
v___y_3915_ = v___y_3931_;
v___y_3916_ = v___y_3932_;
v___y_3917_ = v___y_3933_;
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3938_;
v___y_3920_ = v___y_3939_;
v___y_3921_ = v___x_3748_;
goto v___jp_3906_;
}
else
{
if (v_ctor_3936_ == 0)
{
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
v___y_3910_ = v___y_3926_;
v___y_3911_ = v___y_3927_;
v___y_3912_ = v___y_3928_;
v___y_3913_ = v___y_3929_;
v___y_3914_ = v___y_3930_;
v___y_3915_ = v___y_3931_;
v___y_3916_ = v___y_3932_;
v___y_3917_ = v___y_3933_;
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3938_;
v___y_3920_ = v___y_3939_;
v___y_3921_ = v___x_3941_;
goto v___jp_3906_;
}
else
{
v___y_3871_ = v___y_3923_;
v___y_3872_ = v___y_3924_;
v___y_3873_ = v___y_3925_;
v___y_3874_ = v___y_3926_;
v___y_3875_ = v___y_3927_;
v___y_3876_ = v___y_3928_;
v___y_3877_ = v___y_3929_;
v___y_3878_ = v___y_3930_;
v___y_3879_ = v___y_3931_;
v___y_3880_ = v___y_3932_;
v___y_3881_ = v___y_3933_;
v___y_3882_ = v___y_3937_;
v___y_3883_ = v___y_3939_;
v___y_3884_ = v___y_3938_;
goto v___jp_3870_;
}
}
}
else
{
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
v___y_3910_ = v___y_3926_;
v___y_3911_ = v___y_3927_;
v___y_3912_ = v___y_3928_;
v___y_3913_ = v___y_3929_;
v___y_3914_ = v___y_3930_;
v___y_3915_ = v___y_3931_;
v___y_3916_ = v___y_3932_;
v___y_3917_ = v___y_3933_;
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3938_;
v___y_3920_ = v___y_3939_;
v___y_3921_ = v___x_3748_;
goto v___jp_3906_;
}
}
}
v___jp_3942_:
{
if (v___y_3957_ == 0)
{
uint8_t v_ctor_3958_; 
v_ctor_3958_ = lean_ctor_get_uint8(v___y_3956_, sizeof(void*)*11 + 2);
if (v_ctor_3958_ == 0)
{
if (v___x_3748_ == 0)
{
lean_object* v_size_3959_; lean_object* v_size_3960_; uint8_t v_interpreted_3961_; uint8_t v_ctor_3962_; 
v_size_3959_ = lean_ctor_get(v___y_3956_, 6);
lean_inc(v_size_3959_);
v_size_3960_ = lean_ctor_get(v___y_3953_, 6);
lean_inc(v_size_3960_);
v_interpreted_3961_ = lean_ctor_get_uint8(v___y_3953_, sizeof(void*)*11 + 1);
v_ctor_3962_ = lean_ctor_get_uint8(v___y_3953_, sizeof(void*)*11 + 2);
v___y_3923_ = v___y_3943_;
v___y_3924_ = v___y_3944_;
v___y_3925_ = v___y_3945_;
v___y_3926_ = v___y_3946_;
v___y_3927_ = v___y_3947_;
v___y_3928_ = v___y_3948_;
v___y_3929_ = v___y_3949_;
v___y_3930_ = v___y_3950_;
v___y_3931_ = v___y_3951_;
v___y_3932_ = v___y_3952_;
v___y_3933_ = v___y_3953_;
v_size_3934_ = v_size_3960_;
v_interpreted_3935_ = v_interpreted_3961_;
v_ctor_3936_ = v_ctor_3962_;
v___y_3937_ = v___y_3954_;
v___y_3938_ = v___y_3955_;
v___y_3939_ = v___y_3956_;
v_size_3940_ = v_size_3959_;
goto v___jp_3922_;
}
else
{
v___y_3891_ = v___y_3943_;
v___y_3892_ = v___y_3944_;
v___y_3893_ = v___y_3945_;
v___y_3894_ = v___y_3946_;
v___y_3895_ = v___y_3947_;
v___y_3896_ = v___y_3948_;
v___y_3897_ = v___y_3949_;
v___y_3898_ = v___y_3950_;
v___y_3899_ = v___y_3951_;
v___y_3900_ = v___y_3952_;
v___y_3901_ = v___y_3953_;
v___y_3902_ = v___y_3954_;
v___y_3903_ = v___y_3956_;
v___y_3904_ = v___y_3955_;
goto v___jp_3890_;
}
}
else
{
uint8_t v_ctor_3963_; 
v_ctor_3963_ = lean_ctor_get_uint8(v___y_3953_, sizeof(void*)*11 + 2);
if (v_ctor_3963_ == 0)
{
v___y_3891_ = v___y_3943_;
v___y_3892_ = v___y_3944_;
v___y_3893_ = v___y_3945_;
v___y_3894_ = v___y_3946_;
v___y_3895_ = v___y_3947_;
v___y_3896_ = v___y_3948_;
v___y_3897_ = v___y_3949_;
v___y_3898_ = v___y_3950_;
v___y_3899_ = v___y_3951_;
v___y_3900_ = v___y_3952_;
v___y_3901_ = v___y_3953_;
v___y_3902_ = v___y_3954_;
v___y_3903_ = v___y_3956_;
v___y_3904_ = v___y_3955_;
goto v___jp_3890_;
}
else
{
lean_object* v_size_3964_; lean_object* v_size_3965_; uint8_t v_interpreted_3966_; 
v_size_3964_ = lean_ctor_get(v___y_3956_, 6);
lean_inc(v_size_3964_);
v_size_3965_ = lean_ctor_get(v___y_3953_, 6);
lean_inc(v_size_3965_);
v_interpreted_3966_ = lean_ctor_get_uint8(v___y_3953_, sizeof(void*)*11 + 1);
v___y_3923_ = v___y_3943_;
v___y_3924_ = v___y_3944_;
v___y_3925_ = v___y_3945_;
v___y_3926_ = v___y_3946_;
v___y_3927_ = v___y_3947_;
v___y_3928_ = v___y_3948_;
v___y_3929_ = v___y_3949_;
v___y_3930_ = v___y_3950_;
v___y_3931_ = v___y_3951_;
v___y_3932_ = v___y_3952_;
v___y_3933_ = v___y_3953_;
v_size_3934_ = v_size_3965_;
v_interpreted_3935_ = v_interpreted_3966_;
v_ctor_3936_ = v_ctor_3963_;
v___y_3937_ = v___y_3954_;
v___y_3938_ = v___y_3955_;
v___y_3939_ = v___y_3956_;
v_size_3940_ = v_size_3964_;
goto v___jp_3922_;
}
}
}
else
{
v___y_3891_ = v___y_3943_;
v___y_3892_ = v___y_3944_;
v___y_3893_ = v___y_3945_;
v___y_3894_ = v___y_3946_;
v___y_3895_ = v___y_3947_;
v___y_3896_ = v___y_3948_;
v___y_3897_ = v___y_3949_;
v___y_3898_ = v___y_3950_;
v___y_3899_ = v___y_3951_;
v___y_3900_ = v___y_3952_;
v___y_3901_ = v___y_3953_;
v___y_3902_ = v___y_3954_;
v___y_3903_ = v___y_3956_;
v___y_3904_ = v___y_3955_;
goto v___jp_3890_;
}
}
v___jp_3967_:
{
if (v_interpreted_3970_ == 0)
{
v___y_3943_ = v___y_3973_;
v___y_3944_ = v_trueEqFalse_3972_;
v___y_3945_ = v___y_3979_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3977_;
v___y_3948_ = v___y_3980_;
v___y_3949_ = v___y_3981_;
v___y_3950_ = v___y_3976_;
v___y_3951_ = v___y_3978_;
v___y_3952_ = v___y_3974_;
v___y_3953_ = v___y_3968_;
v___y_3954_ = v_valueInconsistency_3971_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3969_;
v___y_3957_ = v___x_3748_;
goto v___jp_3942_;
}
else
{
uint8_t v_interpreted_3983_; 
v_interpreted_3983_ = lean_ctor_get_uint8(v___y_3968_, sizeof(void*)*11 + 1);
if (v_interpreted_3983_ == 0)
{
v___y_3891_ = v___y_3973_;
v___y_3892_ = v_trueEqFalse_3972_;
v___y_3893_ = v___y_3979_;
v___y_3894_ = v___y_3975_;
v___y_3895_ = v___y_3977_;
v___y_3896_ = v___y_3980_;
v___y_3897_ = v___y_3981_;
v___y_3898_ = v___y_3976_;
v___y_3899_ = v___y_3978_;
v___y_3900_ = v___y_3974_;
v___y_3901_ = v___y_3968_;
v___y_3902_ = v_valueInconsistency_3971_;
v___y_3903_ = v___y_3969_;
v___y_3904_ = v___y_3982_;
goto v___jp_3890_;
}
else
{
v___y_3943_ = v___y_3973_;
v___y_3944_ = v_trueEqFalse_3972_;
v___y_3945_ = v___y_3979_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3977_;
v___y_3948_ = v___y_3980_;
v___y_3949_ = v___y_3981_;
v___y_3950_ = v___y_3976_;
v___y_3951_ = v___y_3978_;
v___y_3952_ = v___y_3974_;
v___y_3953_ = v___y_3968_;
v___y_3954_ = v_valueInconsistency_3971_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3969_;
v___y_3957_ = v___x_3748_;
goto v___jp_3942_;
}
}
}
v___jp_3984_:
{
uint8_t v_interpreted_3999_; 
v_interpreted_3999_ = lean_ctor_get_uint8(v___y_3986_, sizeof(void*)*11 + 1);
v___y_3968_ = v___y_3985_;
v___y_3969_ = v___y_3986_;
v_interpreted_3970_ = v_interpreted_3999_;
v_valueInconsistency_3971_ = v_valueInconsistency_3987_;
v_trueEqFalse_3972_ = v_trueEqFalse_3988_;
v___y_3973_ = v___y_3989_;
v___y_3974_ = v___y_3990_;
v___y_3975_ = v___y_3991_;
v___y_3976_ = v___y_3992_;
v___y_3977_ = v___y_3993_;
v___y_3978_ = v___y_3994_;
v___y_3979_ = v___y_3995_;
v___y_3980_ = v___y_3996_;
v___y_3981_ = v___y_3997_;
v___y_3982_ = v___y_3998_;
goto v___jp_3967_;
}
v___jp_4000_:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4001_, v___y_4007_, v___y_4003_, v___y_4004_, v___y_4008_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_dec_ref(v___x_4013_);
v___y_3985_ = v___y_4009_;
v___y_3986_ = v___y_4010_;
v_valueInconsistency_3987_ = v___x_3748_;
v_trueEqFalse_3988_ = v___x_3889_;
v___y_3989_ = v___y_4001_;
v___y_3990_ = v___y_4011_;
v___y_3991_ = v___y_4002_;
v___y_3992_ = v___y_4012_;
v___y_3993_ = v___y_4005_;
v___y_3994_ = v___y_4006_;
v___y_3995_ = v___y_4007_;
v___y_3996_ = v___y_4003_;
v___y_3997_ = v___y_4004_;
v___y_3998_ = v___y_4008_;
goto v___jp_3984_;
}
else
{
lean_dec(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
return v___x_4013_;
}
}
v___jp_4014_:
{
if (v___y_4021_ == 0)
{
lean_object* v_self_4028_; uint8_t v_interpreted_4029_; lean_object* v_self_4030_; lean_object* v___x_4031_; 
v_self_4028_ = lean_ctor_get(v___y_4025_, 0);
v_interpreted_4029_ = lean_ctor_get_uint8(v___y_4025_, sizeof(void*)*11 + 1);
v_self_4030_ = lean_ctor_get(v___y_4024_, 0);
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4019_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4022_);
lean_inc_ref(v_self_4030_);
lean_inc_ref(v_self_4028_);
v___x_4031_ = l_Lean_Meta_Grind_hasSameType(v_self_4028_, v_self_4030_, v___y_4022_, v___y_4017_, v___y_4019_, v___y_4023_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; uint8_t v___x_4033_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref(v___x_4031_);
v___x_4033_ = lean_unbox(v_a_4032_);
lean_dec(v_a_4032_);
if (v___x_4033_ == 0)
{
v___y_3968_ = v___y_4024_;
v___y_3969_ = v___y_4025_;
v_interpreted_3970_ = v_interpreted_4029_;
v_valueInconsistency_3971_ = v___x_3748_;
v_trueEqFalse_3972_ = v___x_3748_;
v___y_3973_ = v___y_4015_;
v___y_3974_ = v___y_4026_;
v___y_3975_ = v___y_4016_;
v___y_3976_ = v___y_4027_;
v___y_3977_ = v___y_4020_;
v___y_3978_ = v___y_4018_;
v___y_3979_ = v___y_4022_;
v___y_3980_ = v___y_4017_;
v___y_3981_ = v___y_4019_;
v___y_3982_ = v___y_4023_;
goto v___jp_3967_;
}
else
{
v___y_3968_ = v___y_4024_;
v___y_3969_ = v___y_4025_;
v_interpreted_3970_ = v_interpreted_4029_;
v_valueInconsistency_3971_ = v___x_3889_;
v_trueEqFalse_3972_ = v___x_3748_;
v___y_3973_ = v___y_4015_;
v___y_3974_ = v___y_4026_;
v___y_3975_ = v___y_4016_;
v___y_3976_ = v___y_4027_;
v___y_3977_ = v___y_4020_;
v___y_3978_ = v___y_4018_;
v___y_3979_ = v___y_4022_;
v___y_3980_ = v___y_4017_;
v___y_3981_ = v___y_4019_;
v___y_3982_ = v___y_4023_;
goto v___jp_3967_;
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec_ref(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4034_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4031_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4031_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
else
{
v___y_3985_ = v___y_4024_;
v___y_3986_ = v___y_4025_;
v_valueInconsistency_3987_ = v___x_3889_;
v_trueEqFalse_3988_ = v___x_3748_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4026_;
v___y_3991_ = v___y_4016_;
v___y_3992_ = v___y_4027_;
v___y_3993_ = v___y_4020_;
v___y_3994_ = v___y_4018_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4017_;
v___y_3997_ = v___y_4019_;
v___y_3998_ = v___y_4023_;
goto v___jp_3984_;
}
}
v___jp_4042_:
{
if (v___y_4055_ == 0)
{
v___y_3985_ = v___y_4051_;
v___y_3986_ = v___y_4052_;
v_valueInconsistency_3987_ = v___x_3748_;
v_trueEqFalse_3988_ = v___x_3748_;
v___y_3989_ = v___y_4043_;
v___y_3990_ = v___y_4053_;
v___y_3991_ = v___y_4044_;
v___y_3992_ = v___y_4054_;
v___y_3993_ = v___y_4046_;
v___y_3994_ = v___y_4047_;
v___y_3995_ = v___y_4049_;
v___y_3996_ = v___y_4045_;
v___y_3997_ = v___y_4048_;
v___y_3998_ = v___y_4050_;
goto v___jp_3984_;
}
else
{
uint8_t v___x_4056_; 
lean_inc_ref(v_root_3746_);
v___x_4056_ = l_Lean_Expr_isTrue(v_root_3746_);
if (v___x_4056_ == 0)
{
uint8_t v___x_4057_; 
lean_inc_ref(v_root_3747_);
v___x_4057_ = l_Lean_Expr_isTrue(v_root_3747_);
if (v___x_4057_ == 0)
{
if (v_isHEq_3725_ == 0)
{
uint8_t v_heqProofs_4058_; 
v_heqProofs_4058_ = lean_ctor_get_uint8(v___y_4052_, sizeof(void*)*11 + 4);
if (v_heqProofs_4058_ == 0)
{
uint8_t v_heqProofs_4059_; 
v_heqProofs_4059_ = lean_ctor_get_uint8(v___y_4051_, sizeof(void*)*11 + 4);
if (v_heqProofs_4059_ == 0)
{
uint8_t v_interpreted_4060_; 
v_interpreted_4060_ = lean_ctor_get_uint8(v___y_4052_, sizeof(void*)*11 + 1);
v___y_3968_ = v___y_4051_;
v___y_3969_ = v___y_4052_;
v_interpreted_3970_ = v_interpreted_4060_;
v_valueInconsistency_3971_ = v___x_3889_;
v_trueEqFalse_3972_ = v___x_3748_;
v___y_3973_ = v___y_4043_;
v___y_3974_ = v___y_4053_;
v___y_3975_ = v___y_4044_;
v___y_3976_ = v___y_4054_;
v___y_3977_ = v___y_4046_;
v___y_3978_ = v___y_4047_;
v___y_3979_ = v___y_4049_;
v___y_3980_ = v___y_4045_;
v___y_3981_ = v___y_4048_;
v___y_3982_ = v___y_4050_;
goto v___jp_3967_;
}
else
{
v___y_4015_ = v___y_4043_;
v___y_4016_ = v___y_4044_;
v___y_4017_ = v___y_4045_;
v___y_4018_ = v___y_4047_;
v___y_4019_ = v___y_4048_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___x_4057_;
v___y_4022_ = v___y_4049_;
v___y_4023_ = v___y_4050_;
v___y_4024_ = v___y_4051_;
v___y_4025_ = v___y_4052_;
v___y_4026_ = v___y_4053_;
v___y_4027_ = v___y_4054_;
goto v___jp_4014_;
}
}
else
{
v___y_4015_ = v___y_4043_;
v___y_4016_ = v___y_4044_;
v___y_4017_ = v___y_4045_;
v___y_4018_ = v___y_4047_;
v___y_4019_ = v___y_4048_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___x_4057_;
v___y_4022_ = v___y_4049_;
v___y_4023_ = v___y_4050_;
v___y_4024_ = v___y_4051_;
v___y_4025_ = v___y_4052_;
v___y_4026_ = v___y_4053_;
v___y_4027_ = v___y_4054_;
goto v___jp_4014_;
}
}
else
{
v___y_4015_ = v___y_4043_;
v___y_4016_ = v___y_4044_;
v___y_4017_ = v___y_4045_;
v___y_4018_ = v___y_4047_;
v___y_4019_ = v___y_4048_;
v___y_4020_ = v___y_4046_;
v___y_4021_ = v___x_4057_;
v___y_4022_ = v___y_4049_;
v___y_4023_ = v___y_4050_;
v___y_4024_ = v___y_4051_;
v___y_4025_ = v___y_4052_;
v___y_4026_ = v___y_4053_;
v___y_4027_ = v___y_4054_;
goto v___jp_4014_;
}
}
else
{
v___y_4001_ = v___y_4043_;
v___y_4002_ = v___y_4044_;
v___y_4003_ = v___y_4045_;
v___y_4004_ = v___y_4048_;
v___y_4005_ = v___y_4046_;
v___y_4006_ = v___y_4047_;
v___y_4007_ = v___y_4049_;
v___y_4008_ = v___y_4050_;
v___y_4009_ = v___y_4051_;
v___y_4010_ = v___y_4052_;
v___y_4011_ = v___y_4053_;
v___y_4012_ = v___y_4054_;
goto v___jp_4000_;
}
}
else
{
v___y_4001_ = v___y_4043_;
v___y_4002_ = v___y_4044_;
v___y_4003_ = v___y_4045_;
v___y_4004_ = v___y_4048_;
v___y_4005_ = v___y_4046_;
v___y_4006_ = v___y_4047_;
v___y_4007_ = v___y_4049_;
v___y_4008_ = v___y_4050_;
v___y_4009_ = v___y_4051_;
v___y_4010_ = v___y_4052_;
v___y_4011_ = v___y_4053_;
v___y_4012_ = v___y_4054_;
goto v___jp_4000_;
}
}
}
v___jp_4061_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_st_ref_get(v___y_4062_);
lean_inc_ref(v_root_3746_);
v___x_4073_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4072_, v_root_3746_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref(v___x_4073_);
v___x_4075_ = lean_st_ref_get(v___y_4062_);
lean_inc_ref(v_root_3747_);
v___x_4076_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4075_, v_root_3747_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4076_) == 0)
{
uint8_t v_interpreted_4077_; 
v_interpreted_4077_ = lean_ctor_get_uint8(v_a_4074_, sizeof(void*)*11 + 1);
if (v_interpreted_4077_ == 0)
{
lean_object* v_a_4078_; 
v_a_4078_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4078_);
lean_dec_ref(v___x_4076_);
v___y_4043_ = v___y_4062_;
v___y_4044_ = v___y_4064_;
v___y_4045_ = v___y_4069_;
v___y_4046_ = v___y_4066_;
v___y_4047_ = v___y_4067_;
v___y_4048_ = v___y_4070_;
v___y_4049_ = v___y_4068_;
v___y_4050_ = v___y_4071_;
v___y_4051_ = v_a_4078_;
v___y_4052_ = v_a_4074_;
v___y_4053_ = v___y_4063_;
v___y_4054_ = v___y_4065_;
v___y_4055_ = v___x_3748_;
goto v___jp_4042_;
}
else
{
lean_object* v_a_4079_; uint8_t v_interpreted_4080_; 
v_a_4079_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4079_);
lean_dec_ref(v___x_4076_);
v_interpreted_4080_ = lean_ctor_get_uint8(v_a_4079_, sizeof(void*)*11 + 1);
v___y_4043_ = v___y_4062_;
v___y_4044_ = v___y_4064_;
v___y_4045_ = v___y_4069_;
v___y_4046_ = v___y_4066_;
v___y_4047_ = v___y_4067_;
v___y_4048_ = v___y_4070_;
v___y_4049_ = v___y_4068_;
v___y_4050_ = v___y_4071_;
v___y_4051_ = v_a_4079_;
v___y_4052_ = v_a_4074_;
v___y_4053_ = v___y_4063_;
v___y_4054_ = v___y_4065_;
v___y_4055_ = v_interpreted_4080_;
goto v___jp_4042_;
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4074_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4081_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4076_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4076_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4089_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4073_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4073_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
v___jp_4097_:
{
if (lean_obj_tag(v___y_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_a_4099_ = lean_ctor_get(v___y_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref(v___y_4098_);
v___x_4100_ = l_Lean_MessageData_ofExpr(v_a_4099_);
v___x_4101_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_3886_, v___x_4100_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_dec_ref(v___x_4101_);
v___y_4062_ = v_a_3726_;
v___y_4063_ = v_a_3727_;
v___y_4064_ = v_a_3728_;
v___y_4065_ = v_a_3729_;
v___y_4066_ = v_a_3730_;
v___y_4067_ = v_a_3731_;
v___y_4068_ = v_a_3732_;
v___y_4069_ = v_a_3733_;
v___y_4070_ = v_a_3734_;
v___y_4071_ = v_a_3735_;
goto v___jp_4061_;
}
else
{
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
return v___x_4101_;
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4102_ = lean_ctor_get(v___y_4098_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___y_4098_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___y_4098_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___y_4098_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v_a_4116_; uint8_t v___x_4117_; 
lean_dec(v_a_3745_);
lean_dec(v_a_3742_);
lean_dec_ref(v_proof_3724_);
v___x_4114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4115_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4114_, v_a_3734_);
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = lean_unbox(v_a_4116_);
lean_dec(v_a_4116_);
if (v___x_4117_ == 0)
{
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
goto v___jp_3737_;
}
else
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_Meta_Grind_updateLastTag(v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4119_; 
lean_dec_ref(v___x_4118_);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
v___x_4119_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3722_, v_a_3726_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
v___x_4121_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3723_, v_a_3726_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3726_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4120_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
lean_ctor_set(v___x_4125_, 1, v_a_4122_);
v___x_4126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_4114_, v___x_4127_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_dec_ref(v___x_4128_);
goto v___jp_3737_;
}
else
{
return v___x_4128_;
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec(v_a_4120_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
v_a_4129_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4121_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4121_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3726_);
lean_dec_ref(v_rhs_3723_);
v_a_4137_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4119_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4119_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3726_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
return v___x_4118_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_a_3742_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4145_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_3744_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_3744_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_proof_3724_);
lean_dec_ref(v_rhs_3723_);
lean_dec_ref(v_lhs_3722_);
v_a_4153_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_3741_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_3741_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
v___jp_3737_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_box(0);
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4161_, lean_object* v_rhs_4162_, lean_object* v_proof_4163_, lean_object* v_isHEq_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
uint8_t v_isHEq_boxed_4176_; lean_object* v_res_4177_; 
v_isHEq_boxed_4176_ = lean_unbox(v_isHEq_4164_);
v_res_4177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4161_, v_rhs_4162_, v_proof_4163_, v_isHEq_boxed_4176_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4182_; lean_object* v_toGoalState_4183_; lean_object* v_mvarId_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4221_; 
v___x_4182_ = lean_st_ref_take(v_a_4180_);
v_toGoalState_4183_ = lean_ctor_get(v___x_4182_, 0);
v_mvarId_4184_ = lean_ctor_get(v___x_4182_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4186_ = v___x_4182_;
v_isShared_4187_ = v_isSharedCheck_4221_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_mvarId_4184_);
lean_inc(v_toGoalState_4183_);
lean_dec(v___x_4182_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4221_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v_nextDeclIdx_4188_; lean_object* v_canon_4189_; lean_object* v_enodeMap_4190_; lean_object* v_exprs_4191_; lean_object* v_parents_4192_; lean_object* v_congrTable_4193_; lean_object* v_appMap_4194_; lean_object* v_indicesFound_4195_; uint8_t v_inconsistent_4196_; lean_object* v_nextIdx_4197_; lean_object* v_newRawFacts_4198_; lean_object* v_facts_4199_; lean_object* v_extThms_4200_; lean_object* v_ematch_4201_; lean_object* v_inj_4202_; lean_object* v_split_4203_; lean_object* v_clean_4204_; lean_object* v_sstates_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4219_; 
v_nextDeclIdx_4188_ = lean_ctor_get(v_toGoalState_4183_, 0);
v_canon_4189_ = lean_ctor_get(v_toGoalState_4183_, 1);
v_enodeMap_4190_ = lean_ctor_get(v_toGoalState_4183_, 2);
v_exprs_4191_ = lean_ctor_get(v_toGoalState_4183_, 3);
v_parents_4192_ = lean_ctor_get(v_toGoalState_4183_, 4);
v_congrTable_4193_ = lean_ctor_get(v_toGoalState_4183_, 5);
v_appMap_4194_ = lean_ctor_get(v_toGoalState_4183_, 6);
v_indicesFound_4195_ = lean_ctor_get(v_toGoalState_4183_, 7);
v_inconsistent_4196_ = lean_ctor_get_uint8(v_toGoalState_4183_, sizeof(void*)*18);
v_nextIdx_4197_ = lean_ctor_get(v_toGoalState_4183_, 9);
v_newRawFacts_4198_ = lean_ctor_get(v_toGoalState_4183_, 10);
v_facts_4199_ = lean_ctor_get(v_toGoalState_4183_, 11);
v_extThms_4200_ = lean_ctor_get(v_toGoalState_4183_, 12);
v_ematch_4201_ = lean_ctor_get(v_toGoalState_4183_, 13);
v_inj_4202_ = lean_ctor_get(v_toGoalState_4183_, 14);
v_split_4203_ = lean_ctor_get(v_toGoalState_4183_, 15);
v_clean_4204_ = lean_ctor_get(v_toGoalState_4183_, 16);
v_sstates_4205_ = lean_ctor_get(v_toGoalState_4183_, 17);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_toGoalState_4183_);
if (v_isSharedCheck_4219_ == 0)
{
lean_object* v_unused_4220_; 
v_unused_4220_ = lean_ctor_get(v_toGoalState_4183_, 8);
lean_dec(v_unused_4220_);
v___x_4207_ = v_toGoalState_4183_;
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_sstates_4205_);
lean_inc(v_clean_4204_);
lean_inc(v_split_4203_);
lean_inc(v_inj_4202_);
lean_inc(v_ematch_4201_);
lean_inc(v_extThms_4200_);
lean_inc(v_facts_4199_);
lean_inc(v_newRawFacts_4198_);
lean_inc(v_nextIdx_4197_);
lean_inc(v_indicesFound_4195_);
lean_inc(v_appMap_4194_);
lean_inc(v_congrTable_4193_);
lean_inc(v_parents_4192_);
lean_inc(v_exprs_4191_);
lean_inc(v_enodeMap_4190_);
lean_inc(v_canon_4189_);
lean_inc(v_nextDeclIdx_4188_);
lean_dec(v_toGoalState_4183_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4219_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
v___x_4209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 8, v___x_4209_);
v___x_4211_ = v___x_4207_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_nextDeclIdx_4188_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_canon_4189_);
lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_enodeMap_4190_);
lean_ctor_set(v_reuseFailAlloc_4218_, 3, v_exprs_4191_);
lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_parents_4192_);
lean_ctor_set(v_reuseFailAlloc_4218_, 5, v_congrTable_4193_);
lean_ctor_set(v_reuseFailAlloc_4218_, 6, v_appMap_4194_);
lean_ctor_set(v_reuseFailAlloc_4218_, 7, v_indicesFound_4195_);
lean_ctor_set(v_reuseFailAlloc_4218_, 8, v___x_4209_);
lean_ctor_set(v_reuseFailAlloc_4218_, 9, v_nextIdx_4197_);
lean_ctor_set(v_reuseFailAlloc_4218_, 10, v_newRawFacts_4198_);
lean_ctor_set(v_reuseFailAlloc_4218_, 11, v_facts_4199_);
lean_ctor_set(v_reuseFailAlloc_4218_, 12, v_extThms_4200_);
lean_ctor_set(v_reuseFailAlloc_4218_, 13, v_ematch_4201_);
lean_ctor_set(v_reuseFailAlloc_4218_, 14, v_inj_4202_);
lean_ctor_set(v_reuseFailAlloc_4218_, 15, v_split_4203_);
lean_ctor_set(v_reuseFailAlloc_4218_, 16, v_clean_4204_);
lean_ctor_set(v_reuseFailAlloc_4218_, 17, v_sstates_4205_);
lean_ctor_set_uint8(v_reuseFailAlloc_4218_, sizeof(void*)*18, v_inconsistent_4196_);
v___x_4211_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4211_);
v___x_4213_ = v___x_4186_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_mvarId_4184_);
v___x_4213_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = lean_st_ref_set(v_a_4180_, v___x_4213_);
v___x_4215_ = lean_box(0);
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
return v___x_4216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4222_);
lean_dec(v_a_4222_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4225_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec(v_a_4237_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v_toGoalState_4252_; lean_object* v_newFacts_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4251_ = lean_st_ref_get(v_a_4249_);
v_toGoalState_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc_ref(v_toGoalState_4252_);
lean_dec(v___x_4251_);
v_newFacts_4253_ = lean_ctor_get(v_toGoalState_4252_, 8);
lean_inc_ref(v_newFacts_4253_);
lean_dec_ref(v_toGoalState_4252_);
v___x_4254_ = lean_array_get_size(v_newFacts_4253_);
v___x_4255_ = lean_unsigned_to_nat(1u);
v___x_4256_ = lean_nat_sub(v___x_4254_, v___x_4255_);
v___x_4257_ = lean_nat_dec_lt(v___x_4256_, v___x_4254_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_dec(v___x_4256_);
lean_dec_ref(v_newFacts_4253_);
v___x_4258_ = lean_box(0);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
return v___x_4259_;
}
else
{
lean_object* v___x_4260_; lean_object* v_toGoalState_4261_; lean_object* v_mvarId_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4300_; 
v___x_4260_ = lean_st_ref_take(v_a_4249_);
v_toGoalState_4261_ = lean_ctor_get(v___x_4260_, 0);
v_mvarId_4262_ = lean_ctor_get(v___x_4260_, 1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4264_ = v___x_4260_;
v_isShared_4265_ = v_isSharedCheck_4300_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_mvarId_4262_);
lean_inc(v_toGoalState_4261_);
lean_dec(v___x_4260_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4300_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v_nextDeclIdx_4266_; lean_object* v_canon_4267_; lean_object* v_enodeMap_4268_; lean_object* v_exprs_4269_; lean_object* v_parents_4270_; lean_object* v_congrTable_4271_; lean_object* v_appMap_4272_; lean_object* v_indicesFound_4273_; lean_object* v_newFacts_4274_; uint8_t v_inconsistent_4275_; lean_object* v_nextIdx_4276_; lean_object* v_newRawFacts_4277_; lean_object* v_facts_4278_; lean_object* v_extThms_4279_; lean_object* v_ematch_4280_; lean_object* v_inj_4281_; lean_object* v_split_4282_; lean_object* v_clean_4283_; lean_object* v_sstates_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4299_; 
v_nextDeclIdx_4266_ = lean_ctor_get(v_toGoalState_4261_, 0);
v_canon_4267_ = lean_ctor_get(v_toGoalState_4261_, 1);
v_enodeMap_4268_ = lean_ctor_get(v_toGoalState_4261_, 2);
v_exprs_4269_ = lean_ctor_get(v_toGoalState_4261_, 3);
v_parents_4270_ = lean_ctor_get(v_toGoalState_4261_, 4);
v_congrTable_4271_ = lean_ctor_get(v_toGoalState_4261_, 5);
v_appMap_4272_ = lean_ctor_get(v_toGoalState_4261_, 6);
v_indicesFound_4273_ = lean_ctor_get(v_toGoalState_4261_, 7);
v_newFacts_4274_ = lean_ctor_get(v_toGoalState_4261_, 8);
v_inconsistent_4275_ = lean_ctor_get_uint8(v_toGoalState_4261_, sizeof(void*)*18);
v_nextIdx_4276_ = lean_ctor_get(v_toGoalState_4261_, 9);
v_newRawFacts_4277_ = lean_ctor_get(v_toGoalState_4261_, 10);
v_facts_4278_ = lean_ctor_get(v_toGoalState_4261_, 11);
v_extThms_4279_ = lean_ctor_get(v_toGoalState_4261_, 12);
v_ematch_4280_ = lean_ctor_get(v_toGoalState_4261_, 13);
v_inj_4281_ = lean_ctor_get(v_toGoalState_4261_, 14);
v_split_4282_ = lean_ctor_get(v_toGoalState_4261_, 15);
v_clean_4283_ = lean_ctor_get(v_toGoalState_4261_, 16);
v_sstates_4284_ = lean_ctor_get(v_toGoalState_4261_, 17);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_toGoalState_4261_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4286_ = v_toGoalState_4261_;
v_isShared_4287_ = v_isSharedCheck_4299_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_sstates_4284_);
lean_inc(v_clean_4283_);
lean_inc(v_split_4282_);
lean_inc(v_inj_4281_);
lean_inc(v_ematch_4280_);
lean_inc(v_extThms_4279_);
lean_inc(v_facts_4278_);
lean_inc(v_newRawFacts_4277_);
lean_inc(v_nextIdx_4276_);
lean_inc(v_newFacts_4274_);
lean_inc(v_indicesFound_4273_);
lean_inc(v_appMap_4272_);
lean_inc(v_congrTable_4271_);
lean_inc(v_parents_4270_);
lean_inc(v_exprs_4269_);
lean_inc(v_enodeMap_4268_);
lean_inc(v_canon_4267_);
lean_inc(v_nextDeclIdx_4266_);
lean_dec(v_toGoalState_4261_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4299_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4288_ = lean_array_pop(v_newFacts_4274_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 8, v___x_4288_);
v___x_4290_ = v___x_4286_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_nextDeclIdx_4266_);
lean_ctor_set(v_reuseFailAlloc_4298_, 1, v_canon_4267_);
lean_ctor_set(v_reuseFailAlloc_4298_, 2, v_enodeMap_4268_);
lean_ctor_set(v_reuseFailAlloc_4298_, 3, v_exprs_4269_);
lean_ctor_set(v_reuseFailAlloc_4298_, 4, v_parents_4270_);
lean_ctor_set(v_reuseFailAlloc_4298_, 5, v_congrTable_4271_);
lean_ctor_set(v_reuseFailAlloc_4298_, 6, v_appMap_4272_);
lean_ctor_set(v_reuseFailAlloc_4298_, 7, v_indicesFound_4273_);
lean_ctor_set(v_reuseFailAlloc_4298_, 8, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4298_, 9, v_nextIdx_4276_);
lean_ctor_set(v_reuseFailAlloc_4298_, 10, v_newRawFacts_4277_);
lean_ctor_set(v_reuseFailAlloc_4298_, 11, v_facts_4278_);
lean_ctor_set(v_reuseFailAlloc_4298_, 12, v_extThms_4279_);
lean_ctor_set(v_reuseFailAlloc_4298_, 13, v_ematch_4280_);
lean_ctor_set(v_reuseFailAlloc_4298_, 14, v_inj_4281_);
lean_ctor_set(v_reuseFailAlloc_4298_, 15, v_split_4282_);
lean_ctor_set(v_reuseFailAlloc_4298_, 16, v_clean_4283_);
lean_ctor_set(v_reuseFailAlloc_4298_, 17, v_sstates_4284_);
lean_ctor_set_uint8(v_reuseFailAlloc_4298_, sizeof(void*)*18, v_inconsistent_4275_);
v___x_4290_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4292_; 
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4290_);
v___x_4292_ = v___x_4264_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4290_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_mvarId_4262_);
v___x_4292_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4293_ = lean_st_ref_set(v_a_4249_, v___x_4292_);
v___x_4294_ = lean_array_fget(v_newFacts_4253_, v___x_4256_);
lean_dec(v___x_4256_);
lean_dec_ref(v_newFacts_4253_);
v___x_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4301_);
lean_dec(v_a_4301_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4304_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec(v_a_4316_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4328_, lean_object* v_rhs_4329_, lean_object* v_proof_4330_, uint8_t v_isHEq_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___x_4343_; 
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
lean_inc_ref(v_a_4336_);
lean_inc(v_a_4335_);
lean_inc_ref(v_a_4334_);
lean_inc(v_a_4333_);
lean_inc(v_a_4332_);
v___x_4343_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4328_, v_rhs_4329_, v_proof_4330_, v_isHEq_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v___x_4344_; 
lean_dec_ref(v___x_4343_);
v___x_4344_ = lean_grind_process_new_facts(v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
return v___x_4344_;
}
else
{
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec(v_a_4332_);
return v___x_4343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4345_, lean_object* v_rhs_4346_, lean_object* v_proof_4347_, lean_object* v_isHEq_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
uint8_t v_isHEq_boxed_4360_; lean_object* v_res_4361_; 
v_isHEq_boxed_4360_ = lean_unbox(v_isHEq_4348_);
v_res_4361_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4345_, v_rhs_4346_, v_proof_4347_, v_isHEq_boxed_4360_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4362_, lean_object* v_rhs_4363_, lean_object* v_proof_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
uint8_t v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = 0;
v___x_4377_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4362_, v_rhs_4363_, v_proof_4364_, v___x_4376_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4378_, lean_object* v_rhs_4379_, lean_object* v_proof_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4378_, v_rhs_4379_, v_proof_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4393_, lean_object* v_rhs_4394_, lean_object* v_proof_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
uint8_t v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = 1;
v___x_4408_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4393_, v_rhs_4394_, v_proof_4395_, v___x_4407_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4409_, lean_object* v_rhs_4410_, lean_object* v_proof_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4409_, v_rhs_4410_, v_proof_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4427_; lean_object* v_toGoalState_4428_; lean_object* v_mvarId_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4466_; 
v___x_4427_ = lean_st_ref_take(v_a_4425_);
v_toGoalState_4428_ = lean_ctor_get(v___x_4427_, 0);
v_mvarId_4429_ = lean_ctor_get(v___x_4427_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4431_ = v___x_4427_;
v_isShared_4432_ = v_isSharedCheck_4466_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_mvarId_4429_);
lean_inc(v_toGoalState_4428_);
lean_dec(v___x_4427_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4466_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v_nextDeclIdx_4433_; lean_object* v_canon_4434_; lean_object* v_enodeMap_4435_; lean_object* v_exprs_4436_; lean_object* v_parents_4437_; lean_object* v_congrTable_4438_; lean_object* v_appMap_4439_; lean_object* v_indicesFound_4440_; lean_object* v_newFacts_4441_; uint8_t v_inconsistent_4442_; lean_object* v_nextIdx_4443_; lean_object* v_newRawFacts_4444_; lean_object* v_facts_4445_; lean_object* v_extThms_4446_; lean_object* v_ematch_4447_; lean_object* v_inj_4448_; lean_object* v_split_4449_; lean_object* v_clean_4450_; lean_object* v_sstates_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4465_; 
v_nextDeclIdx_4433_ = lean_ctor_get(v_toGoalState_4428_, 0);
v_canon_4434_ = lean_ctor_get(v_toGoalState_4428_, 1);
v_enodeMap_4435_ = lean_ctor_get(v_toGoalState_4428_, 2);
v_exprs_4436_ = lean_ctor_get(v_toGoalState_4428_, 3);
v_parents_4437_ = lean_ctor_get(v_toGoalState_4428_, 4);
v_congrTable_4438_ = lean_ctor_get(v_toGoalState_4428_, 5);
v_appMap_4439_ = lean_ctor_get(v_toGoalState_4428_, 6);
v_indicesFound_4440_ = lean_ctor_get(v_toGoalState_4428_, 7);
v_newFacts_4441_ = lean_ctor_get(v_toGoalState_4428_, 8);
v_inconsistent_4442_ = lean_ctor_get_uint8(v_toGoalState_4428_, sizeof(void*)*18);
v_nextIdx_4443_ = lean_ctor_get(v_toGoalState_4428_, 9);
v_newRawFacts_4444_ = lean_ctor_get(v_toGoalState_4428_, 10);
v_facts_4445_ = lean_ctor_get(v_toGoalState_4428_, 11);
v_extThms_4446_ = lean_ctor_get(v_toGoalState_4428_, 12);
v_ematch_4447_ = lean_ctor_get(v_toGoalState_4428_, 13);
v_inj_4448_ = lean_ctor_get(v_toGoalState_4428_, 14);
v_split_4449_ = lean_ctor_get(v_toGoalState_4428_, 15);
v_clean_4450_ = lean_ctor_get(v_toGoalState_4428_, 16);
v_sstates_4451_ = lean_ctor_get(v_toGoalState_4428_, 17);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_toGoalState_4428_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4453_ = v_toGoalState_4428_;
v_isShared_4454_ = v_isSharedCheck_4465_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_sstates_4451_);
lean_inc(v_clean_4450_);
lean_inc(v_split_4449_);
lean_inc(v_inj_4448_);
lean_inc(v_ematch_4447_);
lean_inc(v_extThms_4446_);
lean_inc(v_facts_4445_);
lean_inc(v_newRawFacts_4444_);
lean_inc(v_nextIdx_4443_);
lean_inc(v_newFacts_4441_);
lean_inc(v_indicesFound_4440_);
lean_inc(v_appMap_4439_);
lean_inc(v_congrTable_4438_);
lean_inc(v_parents_4437_);
lean_inc(v_exprs_4436_);
lean_inc(v_enodeMap_4435_);
lean_inc(v_canon_4434_);
lean_inc(v_nextDeclIdx_4433_);
lean_dec(v_toGoalState_4428_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4465_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4455_ = l_Lean_PersistentArray_push___redArg(v_facts_4445_, v_fact_4424_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 11, v___x_4455_);
v___x_4457_ = v___x_4453_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_nextDeclIdx_4433_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v_canon_4434_);
lean_ctor_set(v_reuseFailAlloc_4464_, 2, v_enodeMap_4435_);
lean_ctor_set(v_reuseFailAlloc_4464_, 3, v_exprs_4436_);
lean_ctor_set(v_reuseFailAlloc_4464_, 4, v_parents_4437_);
lean_ctor_set(v_reuseFailAlloc_4464_, 5, v_congrTable_4438_);
lean_ctor_set(v_reuseFailAlloc_4464_, 6, v_appMap_4439_);
lean_ctor_set(v_reuseFailAlloc_4464_, 7, v_indicesFound_4440_);
lean_ctor_set(v_reuseFailAlloc_4464_, 8, v_newFacts_4441_);
lean_ctor_set(v_reuseFailAlloc_4464_, 9, v_nextIdx_4443_);
lean_ctor_set(v_reuseFailAlloc_4464_, 10, v_newRawFacts_4444_);
lean_ctor_set(v_reuseFailAlloc_4464_, 11, v___x_4455_);
lean_ctor_set(v_reuseFailAlloc_4464_, 12, v_extThms_4446_);
lean_ctor_set(v_reuseFailAlloc_4464_, 13, v_ematch_4447_);
lean_ctor_set(v_reuseFailAlloc_4464_, 14, v_inj_4448_);
lean_ctor_set(v_reuseFailAlloc_4464_, 15, v_split_4449_);
lean_ctor_set(v_reuseFailAlloc_4464_, 16, v_clean_4450_);
lean_ctor_set(v_reuseFailAlloc_4464_, 17, v_sstates_4451_);
lean_ctor_set_uint8(v_reuseFailAlloc_4464_, sizeof(void*)*18, v_inconsistent_4442_);
v___x_4457_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4457_);
v___x_4459_ = v___x_4431_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_mvarId_4429_);
v___x_4459_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4460_ = lean_st_ref_set(v_a_4425_, v___x_4459_);
v___x_4461_ = lean_box(0);
v___x_4462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
return v___x_4462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4467_, v_a_4468_);
lean_dec(v_a_4468_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4471_, v_a_4472_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
lean_dec(v_a_4494_);
lean_dec_ref(v_a_4493_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
lean_dec(v_a_4486_);
lean_dec(v_a_4485_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4497_, lean_object* v_rhs_4498_, lean_object* v_proof_4499_, lean_object* v_generation_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v___x_4512_; 
lean_inc(v_a_4510_);
lean_inc_ref(v_a_4509_);
lean_inc(v_a_4508_);
lean_inc_ref(v_a_4507_);
lean_inc_ref(v_rhs_4498_);
lean_inc_ref(v_lhs_4497_);
v___x_4512_ = l_Lean_Meta_mkEq(v_lhs_4497_, v_rhs_4498_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4524_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref(v___x_4512_);
lean_inc(v_a_4513_);
v___x_4514_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4513_, v_a_4501_);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; 
v_unused_4525_ = lean_ctor_get(v___x_4514_, 0);
lean_dec(v_unused_4525_);
v___x_4516_ = v___x_4514_;
v_isShared_4517_ = v_isSharedCheck_4524_;
goto v_resetjp_4515_;
}
else
{
lean_dec(v___x_4514_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4524_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set_tag(v___x_4516_, 1);
lean_ctor_set(v___x_4516_, 0, v_a_4513_);
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4513_);
v___x_4519_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4520_; 
lean_inc(v_a_4510_);
lean_inc_ref(v_a_4509_);
lean_inc(v_a_4508_);
lean_inc_ref(v_a_4507_);
lean_inc(v_a_4506_);
lean_inc_ref(v_a_4505_);
lean_inc(v_a_4504_);
lean_inc_ref(v_a_4503_);
lean_inc(v_a_4502_);
lean_inc(v_a_4501_);
lean_inc_ref(v___x_4519_);
lean_inc(v_generation_4500_);
lean_inc_ref(v_lhs_4497_);
v___x_4520_ = lean_grind_internalize(v_lhs_4497_, v_generation_4500_, v___x_4519_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v___x_4521_; 
lean_dec_ref(v___x_4520_);
lean_inc(v_a_4510_);
lean_inc_ref(v_a_4509_);
lean_inc(v_a_4508_);
lean_inc_ref(v_a_4507_);
lean_inc(v_a_4506_);
lean_inc_ref(v_a_4505_);
lean_inc(v_a_4504_);
lean_inc_ref(v_a_4503_);
lean_inc(v_a_4502_);
lean_inc(v_a_4501_);
lean_inc_ref(v_rhs_4498_);
v___x_4521_ = lean_grind_internalize(v_rhs_4498_, v_generation_4500_, v___x_4519_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v___x_4522_; 
lean_dec_ref(v___x_4521_);
v___x_4522_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4497_, v_rhs_4498_, v_proof_4499_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
return v___x_4522_;
}
else
{
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_proof_4499_);
lean_dec_ref(v_rhs_4498_);
lean_dec_ref(v_lhs_4497_);
return v___x_4521_;
}
}
else
{
lean_dec_ref(v___x_4519_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec(v_generation_4500_);
lean_dec_ref(v_proof_4499_);
lean_dec_ref(v_rhs_4498_);
lean_dec_ref(v_lhs_4497_);
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec(v_generation_4500_);
lean_dec_ref(v_proof_4499_);
lean_dec_ref(v_rhs_4498_);
lean_dec_ref(v_lhs_4497_);
v_a_4526_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4512_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4512_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4534_, lean_object* v_rhs_4535_, lean_object* v_proof_4536_, lean_object* v_generation_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4534_, v_rhs_4535_, v_proof_4536_, v_generation_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4550_, lean_object* v_generation_4551_, lean_object* v_p_4552_, uint8_t v_isNeg_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_box(0);
lean_inc(v_a_4563_);
lean_inc_ref(v_a_4562_);
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
lean_inc(v_a_4559_);
lean_inc_ref(v_a_4558_);
lean_inc(v_a_4557_);
lean_inc_ref(v_a_4556_);
lean_inc(v_a_4555_);
lean_inc(v_a_4554_);
lean_inc_ref(v_p_4552_);
v___x_4566_ = lean_grind_internalize(v_p_4552_, v_generation_4551_, v___x_4565_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_dec_ref(v___x_4566_);
if (v_isNeg_4553_ == 0)
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4558_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4569_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref(v___x_4567_);
lean_inc(v_a_4563_);
lean_inc_ref(v_a_4562_);
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
v___x_4569_ = l_Lean_Meta_mkEqTrue(v_proof_4550_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4571_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref(v___x_4569_);
v___x_4571_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4552_, v_a_4568_, v_a_4570_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
return v___x_4571_;
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4568_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_p_4552_);
v_a_4572_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4569_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4569_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_p_4552_);
lean_dec_ref(v_proof_4550_);
v_a_4580_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4567_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4567_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
else
{
lean_object* v___x_4588_; 
v___x_4588_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4558_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; lean_object* v___x_4590_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_a_4589_);
lean_dec_ref(v___x_4588_);
lean_inc(v_a_4563_);
lean_inc_ref(v_a_4562_);
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
v___x_4590_ = l_Lean_Meta_mkEqFalse(v_proof_4550_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4592_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref(v___x_4590_);
v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4552_, v_a_4589_, v_a_4591_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
return v___x_4592_;
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec(v_a_4589_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_p_4552_);
v_a_4593_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4590_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4590_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_p_4552_);
lean_dec_ref(v_proof_4550_);
v_a_4601_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4588_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4588_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
else
{
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_p_4552_);
lean_dec_ref(v_proof_4550_);
return v___x_4566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4609_, lean_object* v_generation_4610_, lean_object* v_p_4611_, lean_object* v_isNeg_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
uint8_t v_isNeg_boxed_4624_; lean_object* v_res_4625_; 
v_isNeg_boxed_4624_ = lean_unbox(v_isNeg_4612_);
v_res_4625_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4609_, v_generation_4610_, v_p_4611_, v_isNeg_boxed_4624_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4626_, lean_object* v_generation_4627_, lean_object* v_p_4628_, lean_object* v_lhs_4629_, lean_object* v_rhs_4630_, uint8_t v_isNeg_4631_, uint8_t v_isHEq_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
if (v_isNeg_4631_ == 0)
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_p_4628_);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
lean_inc(v_a_4638_);
lean_inc_ref(v_a_4637_);
lean_inc(v_a_4636_);
lean_inc_ref(v_a_4635_);
lean_inc(v_a_4634_);
lean_inc(v_a_4633_);
lean_inc_ref(v___x_4644_);
lean_inc(v_generation_4627_);
lean_inc_ref(v_lhs_4629_);
v___x_4645_ = lean_grind_internalize(v_lhs_4629_, v_generation_4627_, v___x_4644_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v___x_4646_; 
lean_dec_ref(v___x_4645_);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
lean_inc(v_a_4638_);
lean_inc_ref(v_a_4637_);
lean_inc(v_a_4636_);
lean_inc_ref(v_a_4635_);
lean_inc(v_a_4634_);
lean_inc(v_a_4633_);
lean_inc_ref(v_rhs_4630_);
v___x_4646_ = lean_grind_internalize(v_rhs_4630_, v_generation_4627_, v___x_4644_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v___x_4647_; 
lean_dec_ref(v___x_4646_);
v___x_4647_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4629_, v_rhs_4630_, v_proof_4626_, v_isHEq_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
return v___x_4647_;
}
else
{
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_rhs_4630_);
lean_dec_ref(v_lhs_4629_);
lean_dec_ref(v_proof_4626_);
return v___x_4646_;
}
}
else
{
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_rhs_4630_);
lean_dec_ref(v_lhs_4629_);
lean_dec(v_generation_4627_);
lean_dec_ref(v_proof_4626_);
return v___x_4645_;
}
}
else
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
lean_dec_ref(v_rhs_4630_);
lean_dec_ref(v_lhs_4629_);
v___x_4648_ = lean_box(0);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
lean_inc(v_a_4638_);
lean_inc_ref(v_a_4637_);
lean_inc(v_a_4636_);
lean_inc_ref(v_a_4635_);
lean_inc(v_a_4634_);
lean_inc(v_a_4633_);
lean_inc_ref(v_p_4628_);
v___x_4649_ = lean_grind_internalize(v_p_4628_, v_generation_4627_, v___x_4648_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v___x_4650_; 
lean_dec_ref(v___x_4649_);
v___x_4650_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4637_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4652_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref(v___x_4650_);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
v___x_4652_ = l_Lean_Meta_mkEqFalse(v_proof_4626_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4654_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4652_);
v___x_4654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4628_, v_a_4651_, v_a_4653_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
return v___x_4654_;
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec(v_a_4651_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_p_4628_);
v_a_4655_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4652_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4652_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_p_4628_);
lean_dec_ref(v_proof_4626_);
v_a_4663_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4650_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4650_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
else
{
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_p_4628_);
lean_dec_ref(v_proof_4626_);
return v___x_4649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4671_ = _args[0];
lean_object* v_generation_4672_ = _args[1];
lean_object* v_p_4673_ = _args[2];
lean_object* v_lhs_4674_ = _args[3];
lean_object* v_rhs_4675_ = _args[4];
lean_object* v_isNeg_4676_ = _args[5];
lean_object* v_isHEq_4677_ = _args[6];
lean_object* v_a_4678_ = _args[7];
lean_object* v_a_4679_ = _args[8];
lean_object* v_a_4680_ = _args[9];
lean_object* v_a_4681_ = _args[10];
lean_object* v_a_4682_ = _args[11];
lean_object* v_a_4683_ = _args[12];
lean_object* v_a_4684_ = _args[13];
lean_object* v_a_4685_ = _args[14];
lean_object* v_a_4686_ = _args[15];
lean_object* v_a_4687_ = _args[16];
lean_object* v_a_4688_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4689_; uint8_t v_isHEq_boxed_4690_; lean_object* v_res_4691_; 
v_isNeg_boxed_4689_ = lean_unbox(v_isNeg_4676_);
v_isHEq_boxed_4690_ = lean_unbox(v_isHEq_4677_);
v_res_4691_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4671_, v_generation_4672_, v_p_4673_, v_lhs_4674_, v_rhs_4675_, v_isNeg_boxed_4689_, v_isHEq_boxed_4690_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4695_, lean_object* v_generation_4696_, lean_object* v_p_4697_, uint8_t v_isNeg_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v___x_4710_; 
lean_inc_ref(v_p_4697_);
v___x_4710_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4697_, v_a_4706_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref(v___x_4710_);
v___x_4712_ = l_Lean_Expr_cleanupAnnotations(v_a_4711_);
v___x_4713_ = l_Lean_Expr_isApp(v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; 
lean_dec_ref(v___x_4712_);
v___x_4714_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4714_;
}
else
{
lean_object* v_arg_4715_; lean_object* v___x_4716_; uint8_t v___x_4717_; 
v_arg_4715_ = lean_ctor_get(v___x_4712_, 1);
lean_inc_ref(v_arg_4715_);
v___x_4716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4712_);
v___x_4717_ = l_Lean_Expr_isApp(v___x_4716_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4718_; 
lean_dec_ref(v___x_4716_);
lean_dec_ref(v_arg_4715_);
v___x_4718_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4718_;
}
else
{
lean_object* v_arg_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v_arg_4719_ = lean_ctor_get(v___x_4716_, 1);
lean_inc_ref(v_arg_4719_);
v___x_4720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4716_);
v___x_4721_ = l_Lean_Expr_isApp(v___x_4720_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
lean_dec_ref(v___x_4720_);
lean_dec_ref(v_arg_4719_);
lean_dec_ref(v_arg_4715_);
v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4722_;
}
else
{
lean_object* v_arg_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v_arg_4723_ = lean_ctor_get(v___x_4720_, 1);
lean_inc_ref(v_arg_4723_);
v___x_4724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4720_);
v___x_4725_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4726_ = l_Lean_Expr_isConstOf(v___x_4724_, v___x_4725_);
if (v___x_4726_ == 0)
{
uint8_t v___x_4727_; 
lean_dec_ref(v_arg_4719_);
v___x_4727_ = l_Lean_Expr_isApp(v___x_4724_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
lean_dec_ref(v___x_4724_);
lean_dec_ref(v_arg_4723_);
lean_dec_ref(v_arg_4715_);
v___x_4728_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4728_;
}
else
{
lean_object* v___x_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v___x_4729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4724_);
v___x_4730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4731_ = l_Lean_Expr_isConstOf(v___x_4729_, v___x_4730_);
lean_dec_ref(v___x_4729_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; 
lean_dec_ref(v_arg_4723_);
lean_dec_ref(v_arg_4715_);
v___x_4732_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4732_;
}
else
{
lean_object* v___x_4733_; 
v___x_4733_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4695_, v_generation_4696_, v_p_4697_, v_arg_4723_, v_arg_4715_, v_isNeg_4698_, v___x_4731_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4733_;
}
}
}
else
{
uint8_t v___x_4734_; 
lean_dec_ref(v___x_4724_);
v___x_4734_ = l_Lean_Expr_isProp(v_arg_4723_);
lean_dec_ref(v_arg_4723_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4695_, v_generation_4696_, v_p_4697_, v_arg_4719_, v_arg_4715_, v_isNeg_4698_, v___x_4734_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4735_;
}
else
{
lean_object* v___x_4736_; 
lean_dec_ref(v_arg_4719_);
lean_dec_ref(v_arg_4715_);
v___x_4736_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4695_, v_generation_4696_, v_p_4697_, v_isNeg_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4736_;
}
}
}
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_p_4697_);
lean_dec(v_generation_4696_);
lean_dec_ref(v_proof_4695_);
v_a_4737_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4710_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4710_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_4745_, lean_object* v_generation_4746_, lean_object* v_p_4747_, lean_object* v_isNeg_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
uint8_t v_isNeg_boxed_4760_; lean_object* v_res_4761_; 
v_isNeg_boxed_4760_ = lean_unbox(v_isNeg_4748_);
v_res_4761_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4745_, v_generation_4746_, v_p_4747_, v_isNeg_boxed_4760_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_4769_, lean_object* v_proof_4770_, lean_object* v_generation_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v___y_4784_; lean_object* v___y_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; lean_object* v___y_4801_; lean_object* v___y_4802_; lean_object* v___y_4803_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___y_4806_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v_a_4817_; uint8_t v___x_4818_; 
lean_inc_ref(v_fact_4769_);
v___x_4814_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4769_, v_a_4772_);
lean_dec_ref(v___x_4814_);
v___x_4815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_4816_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4815_, v_a_4780_);
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc(v_a_4817_);
lean_dec_ref(v___x_4816_);
v___x_4818_ = lean_unbox(v_a_4817_);
lean_dec(v_a_4817_);
if (v___x_4818_ == 0)
{
v___y_4797_ = v_a_4772_;
v___y_4798_ = v_a_4773_;
v___y_4799_ = v_a_4774_;
v___y_4800_ = v_a_4775_;
v___y_4801_ = v_a_4776_;
v___y_4802_ = v_a_4777_;
v___y_4803_ = v_a_4778_;
v___y_4804_ = v_a_4779_;
v___y_4805_ = v_a_4780_;
v___y_4806_ = v_a_4781_;
goto v___jp_4796_;
}
else
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_Meta_Grind_updateLastTag(v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_dec_ref(v___x_4819_);
lean_inc_ref(v_fact_4769_);
v___x_4820_ = l_Lean_MessageData_ofExpr(v_fact_4769_);
v___x_4821_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_4815_, v___x_4820_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_dec_ref(v___x_4821_);
v___y_4797_ = v_a_4772_;
v___y_4798_ = v_a_4773_;
v___y_4799_ = v_a_4774_;
v___y_4800_ = v_a_4775_;
v___y_4801_ = v_a_4776_;
v___y_4802_ = v_a_4777_;
v___y_4803_ = v_a_4778_;
v___y_4804_ = v_a_4779_;
v___y_4805_ = v_a_4780_;
v___y_4806_ = v_a_4781_;
goto v___jp_4796_;
}
else
{
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec(v_generation_4771_);
lean_dec_ref(v_proof_4770_);
lean_dec_ref(v_fact_4769_);
return v___x_4821_;
}
}
else
{
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec(v_generation_4771_);
lean_dec_ref(v_proof_4770_);
lean_dec_ref(v_fact_4769_);
return v___x_4819_;
}
}
v___jp_4783_:
{
uint8_t v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = 0;
v___x_4795_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4770_, v_generation_4771_, v_fact_4769_, v___x_4794_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
return v___x_4795_;
}
v___jp_4796_:
{
lean_object* v___x_4807_; uint8_t v___x_4808_; 
lean_inc_ref(v_fact_4769_);
v___x_4807_ = l_Lean_Expr_cleanupAnnotations(v_fact_4769_);
v___x_4808_ = l_Lean_Expr_isApp(v___x_4807_);
if (v___x_4808_ == 0)
{
lean_dec_ref(v___x_4807_);
v___y_4784_ = v___y_4797_;
v___y_4785_ = v___y_4798_;
v___y_4786_ = v___y_4799_;
v___y_4787_ = v___y_4800_;
v___y_4788_ = v___y_4801_;
v___y_4789_ = v___y_4802_;
v___y_4790_ = v___y_4803_;
v___y_4791_ = v___y_4804_;
v___y_4792_ = v___y_4805_;
v___y_4793_ = v___y_4806_;
goto v___jp_4783_;
}
else
{
lean_object* v_arg_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v_arg_4809_ = lean_ctor_get(v___x_4807_, 1);
lean_inc_ref(v_arg_4809_);
v___x_4810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4807_);
v___x_4811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_4812_ = l_Lean_Expr_isConstOf(v___x_4810_, v___x_4811_);
lean_dec_ref(v___x_4810_);
if (v___x_4812_ == 0)
{
lean_dec_ref(v_arg_4809_);
v___y_4784_ = v___y_4797_;
v___y_4785_ = v___y_4798_;
v___y_4786_ = v___y_4799_;
v___y_4787_ = v___y_4800_;
v___y_4788_ = v___y_4801_;
v___y_4789_ = v___y_4802_;
v___y_4790_ = v___y_4803_;
v___y_4791_ = v___y_4804_;
v___y_4792_ = v___y_4805_;
v___y_4793_ = v___y_4806_;
goto v___jp_4783_;
}
else
{
lean_object* v___x_4813_; 
lean_dec_ref(v_fact_4769_);
v___x_4813_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4770_, v_generation_4771_, v_arg_4809_, v___x_4812_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_4822_, lean_object* v_proof_4823_, lean_object* v_generation_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_4822_, v_proof_4823_, v_generation_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4840_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; uint8_t v___x_4853_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref(v___x_4851_);
v___x_4853_ = lean_unbox(v_a_4852_);
lean_dec(v_a_4852_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__3___redArg___closed__0));
v___x_4855_ = l_Lean_Core_checkSystem(v___x_4854_, v___y_4848_, v___y_4849_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v___x_4856_; 
lean_dec_ref(v___x_4855_);
v___x_4856_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_4840_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4893_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4859_ = v___x_4856_;
v_isShared_4860_ = v_isSharedCheck_4893_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4856_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4893_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
if (lean_obj_tag(v_a_4857_) == 1)
{
lean_object* v_val_4861_; 
lean_del_object(v___x_4859_);
v_val_4861_ = lean_ctor_get(v_a_4857_, 0);
lean_inc(v_val_4861_);
lean_dec_ref(v_a_4857_);
if (lean_obj_tag(v_val_4861_) == 0)
{
lean_object* v_lhs_4862_; lean_object* v_rhs_4863_; lean_object* v_proof_4864_; uint8_t v_isHEq_4865_; lean_object* v___x_4866_; 
v_lhs_4862_ = lean_ctor_get(v_val_4861_, 0);
lean_inc_ref(v_lhs_4862_);
v_rhs_4863_ = lean_ctor_get(v_val_4861_, 1);
lean_inc_ref(v_rhs_4863_);
v_proof_4864_ = lean_ctor_get(v_val_4861_, 2);
lean_inc_ref(v_proof_4864_);
v_isHEq_4865_ = lean_ctor_get_uint8(v_val_4861_, sizeof(void*)*3);
lean_dec_ref(v_val_4861_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
lean_inc_ref(v___y_4846_);
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
lean_inc(v___y_4841_);
lean_inc(v___y_4840_);
v___x_4866_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4862_, v_rhs_4863_, v_proof_4864_, v_isHEq_4865_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_dec_ref(v___x_4866_);
goto _start;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v_a_4868_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4866_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4866_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
else
{
lean_object* v_prop_4876_; lean_object* v_proof_4877_; lean_object* v_generation_4878_; lean_object* v___x_4879_; 
v_prop_4876_ = lean_ctor_get(v_val_4861_, 0);
lean_inc_ref(v_prop_4876_);
v_proof_4877_ = lean_ctor_get(v_val_4861_, 1);
lean_inc_ref(v_proof_4877_);
v_generation_4878_ = lean_ctor_get(v_val_4861_, 2);
lean_inc(v_generation_4878_);
lean_dec_ref(v_val_4861_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
lean_inc(v___y_4847_);
lean_inc_ref(v___y_4846_);
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
lean_inc(v___y_4841_);
lean_inc(v___y_4840_);
v___x_4879_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_4876_, v_proof_4877_, v_generation_4878_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_dec_ref(v___x_4879_);
goto _start;
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v_a_4881_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4879_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4879_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
lean_dec(v_a_4857_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v___x_4889_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_4860_ == 0)
{
lean_ctor_set(v___x_4859_, 0, v___x_4889_);
v___x_4891_ = v___x_4859_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v_a_4894_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4856_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4856_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4894_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v_a_4902_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4855_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4855_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v___x_4910_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
v___x_4910_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_4840_);
lean_dec(v___y_4840_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4918_; 
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; 
v_unused_4919_ = lean_ctor_get(v___x_4910_, 0);
lean_dec(v_unused_4919_);
v___x_4912_ = v___x_4910_;
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
else
{
lean_dec(v___x_4910_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4918_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4914_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4914_);
v___x_4916_ = v___x_4912_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
v_a_4920_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4910_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4910_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec(v___y_4840_);
v_a_4928_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4851_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4851_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4973_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4962_ = v___x_4959_;
v_isShared_4963_ = v_isSharedCheck_4973_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4973_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_fst_4964_; 
v_fst_4964_ = lean_ctor_get(v_a_4960_, 0);
lean_inc(v_fst_4964_);
lean_dec(v_a_4960_);
if (lean_obj_tag(v_fst_4964_) == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4967_; 
v___x_4965_ = lean_box(0);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v___x_4965_);
v___x_4967_ = v___x_4962_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4965_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
else
{
lean_object* v_val_4969_; lean_object* v___x_4971_; 
v_val_4969_ = lean_ctor_get(v_fst_4964_, 0);
lean_inc(v_val_4969_);
lean_dec_ref(v_fst_4964_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v_val_4969_);
v___x_4971_ = v___x_4962_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_val_4969_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
else
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4981_; 
v_a_4974_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4976_ = v___x_4959_;
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4959_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4979_; 
if (v_isShared_4977_ == 0)
{
v___x_4979_ = v___x_4976_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4974_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = lean_grind_process_new_facts(v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___x_5006_; 
v___x_5006_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_b_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_b_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
lean_dec_ref(v_b_5007_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5020_, lean_object* v_proof_5021_, lean_object* v_generation_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
uint8_t v___x_5034_; 
lean_inc_ref(v_fact_5020_);
v___x_5034_ = l_Lean_Expr_isTrue(v_fact_5020_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5023_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5047_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5038_ = v___x_5035_;
v_isShared_5039_ = v_isSharedCheck_5047_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5035_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5047_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
uint8_t v___x_5040_; 
v___x_5040_ = lean_unbox(v_a_5036_);
lean_dec(v_a_5036_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
lean_del_object(v___x_5038_);
v___x_5041_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5023_);
lean_dec_ref(v___x_5041_);
v___x_5042_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5020_, v_proof_5021_, v_generation_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_);
return v___x_5042_;
}
else
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec(v_a_5023_);
lean_dec(v_generation_5022_);
lean_dec_ref(v_proof_5021_);
lean_dec_ref(v_fact_5020_);
v___x_5043_ = lean_box(0);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 0, v___x_5043_);
v___x_5045_ = v___x_5038_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec(v_a_5023_);
lean_dec(v_generation_5022_);
lean_dec_ref(v_proof_5021_);
lean_dec_ref(v_fact_5020_);
v_a_5048_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5035_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5035_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
else
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec(v_a_5023_);
lean_dec(v_generation_5022_);
lean_dec_ref(v_proof_5021_);
lean_dec_ref(v_fact_5020_);
v___x_5056_ = lean_box(0);
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
return v___x_5057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5058_, lean_object* v_proof_5059_, lean_object* v_generation_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Lean_Meta_Grind_add(v_fact_5058_, v_proof_5059_, v_generation_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5073_, lean_object* v_generation_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v___x_5086_; 
lean_inc_ref(v_a_5081_);
lean_inc(v_fvarId_5073_);
v___x_5086_ = l_Lean_FVarId_getType___redArg(v_fvarId_5073_, v_a_5081_, v_a_5083_, v_a_5084_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref(v___x_5086_);
v___x_5088_ = l_Lean_mkFVar(v_fvarId_5073_);
v___x_5089_ = l_Lean_Meta_Grind_add(v_a_5087_, v___x_5088_, v_generation_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
return v___x_5089_;
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec(v_generation_5074_);
lean_dec(v_fvarId_5073_);
v_a_5090_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5086_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5086_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5098_, lean_object* v_generation_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5098_, v_generation_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
return v_res_5111_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Core(builtin);
}
#ifdef __cplusplus
}
#endif
