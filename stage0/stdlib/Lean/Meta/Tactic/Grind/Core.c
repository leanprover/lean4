// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Core
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Inv import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Tactic.Grind.PP import Lean.Meta.Tactic.Grind.Ctor import Lean.Meta.Tactic.Grind.Beta import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Internalize import Init.Omega
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
extern lean_object* l_Lean_eagerReflBoolFalse;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_PendingSolverPropagations_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_DelayedTheoremInstance_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_resetParentsOf___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_copyParentsTo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isCongrRoot(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_ppENodeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsInconsistent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_process_to_do(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_newEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_newDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(5, 81, 119, 21, 241, 124, 41, 97)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "remove: "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "curr: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "parent: "};
static const lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fn: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", parents: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " new root "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "adding "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 244, 178, 10, 61, 92, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " and "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " are already in the same equivalence class"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 181, 250, 47, 64, 71, 92, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v___x_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_self_14_; lean_object* v_next_15_; lean_object* v_root_16_; lean_object* v_congr_17_; lean_object* v_target_x3f_18_; lean_object* v_proof_x3f_19_; uint8_t v_flipped_20_; lean_object* v_size_21_; uint8_t v_interpreted_22_; uint8_t v_ctor_23_; uint8_t v_hasLambdas_24_; uint8_t v_heqProofs_25_; lean_object* v_idx_26_; lean_object* v_generation_27_; lean_object* v_mt_28_; lean_object* v_sTerms_29_; uint8_t v_funCC_30_; lean_object* v_ematchDiagSource_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_54_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v___x_12_, 1);
v_self_14_ = lean_ctor_get(v_a_13_, 0);
v_next_15_ = lean_ctor_get(v_a_13_, 1);
v_root_16_ = lean_ctor_get(v_a_13_, 2);
v_congr_17_ = lean_ctor_get(v_a_13_, 3);
v_target_x3f_18_ = lean_ctor_get(v_a_13_, 4);
v_proof_x3f_19_ = lean_ctor_get(v_a_13_, 5);
v_flipped_20_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12);
v_size_21_ = lean_ctor_get(v_a_13_, 6);
v_interpreted_22_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12 + 1);
v_ctor_23_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12 + 2);
v_hasLambdas_24_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12 + 3);
v_heqProofs_25_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12 + 4);
v_idx_26_ = lean_ctor_get(v_a_13_, 7);
v_generation_27_ = lean_ctor_get(v_a_13_, 8);
v_mt_28_ = lean_ctor_get(v_a_13_, 9);
v_sTerms_29_ = lean_ctor_get(v_a_13_, 10);
v_funCC_30_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*12 + 5);
v_ematchDiagSource_31_ = lean_ctor_get(v_a_13_, 11);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_54_ == 0)
{
v___x_33_ = v_a_13_;
v_isShared_34_ = v_isSharedCheck_54_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_ematchDiagSource_31_);
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
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_54_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___y_36_; 
if (lean_obj_tag(v_target_x3f_18_) == 1)
{
lean_object* v_val_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_53_; 
v_val_41_ = lean_ctor_get(v_target_x3f_18_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_target_x3f_18_);
if (v_isSharedCheck_53_ == 0)
{
v___x_43_ = v_target_x3f_18_;
v_isShared_44_ = v_isSharedCheck_53_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_val_41_);
lean_dec(v_target_x3f_18_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_53_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v___y_46_; 
if (v_flipped_20_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
v___y_46_ = v___x_51_;
goto v___jp_45_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
v___y_46_ = v___x_52_;
goto v___jp_45_;
}
v___jp_45_:
{
lean_object* v___x_48_; 
lean_inc_ref(v_e_1_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v_e_1_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_e_1_);
v___x_48_ = v_reuseFailAlloc_50_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_val_41_, v___y_46_, v___x_48_, v_proof_x3f_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_dec_ref_known(v___x_49_, 1);
v___y_36_ = v_a_5_;
goto v___jp_35_;
}
else
{
lean_del_object(v___x_33_);
lean_dec(v_ematchDiagSource_31_);
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
return v___x_49_;
}
}
}
}
}
else
{
lean_dec(v_proof_x3f_19_);
lean_dec(v_target_x3f_18_);
v___y_36_ = v_a_5_;
goto v___jp_35_;
}
v___jp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v___x_33_, 4, v_targetNew_x3f_3_);
v___x_38_ = v___x_33_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_self_14_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_next_15_);
lean_ctor_set(v_reuseFailAlloc_40_, 2, v_root_16_);
lean_ctor_set(v_reuseFailAlloc_40_, 3, v_congr_17_);
lean_ctor_set(v_reuseFailAlloc_40_, 4, v_targetNew_x3f_3_);
lean_ctor_set(v_reuseFailAlloc_40_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v_reuseFailAlloc_40_, 6, v_size_21_);
lean_ctor_set(v_reuseFailAlloc_40_, 7, v_idx_26_);
lean_ctor_set(v_reuseFailAlloc_40_, 8, v_generation_27_);
lean_ctor_set(v_reuseFailAlloc_40_, 9, v_mt_28_);
lean_ctor_set(v_reuseFailAlloc_40_, 10, v_sTerms_29_);
lean_ctor_set(v_reuseFailAlloc_40_, 11, v_ematchDiagSource_31_);
lean_ctor_set_uint8(v_reuseFailAlloc_40_, sizeof(void*)*12 + 1, v_interpreted_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_40_, sizeof(void*)*12 + 2, v_ctor_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_40_, sizeof(void*)*12 + 3, v_hasLambdas_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_40_, sizeof(void*)*12 + 4, v_heqProofs_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_40_, sizeof(void*)*12 + 5, v_funCC_30_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*12, v_flippedNew_2_);
v___x_39_ = l_Lean_Meta_Grind_setENode___redArg(v_e_1_, v___x_38_, v___y_36_);
return v___x_39_;
}
}
}
}
else
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
lean_dec(v_proofNew_x3f_4_);
lean_dec(v_targetNew_x3f_3_);
lean_dec_ref(v_e_1_);
v_a_55_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v___x_12_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_12_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* v_e_63_, lean_object* v_flippedNew_64_, lean_object* v_targetNew_x3f_65_, lean_object* v_proofNew_x3f_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
uint8_t v_flippedNew_boxed_73_; lean_object* v_res_74_; 
v_flippedNew_boxed_73_ = lean_unbox(v_flippedNew_64_);
v_res_74_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_63_, v_flippedNew_boxed_73_, v_targetNew_x3f_65_, v_proofNew_x3f_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* v_e_75_, uint8_t v_flippedNew_76_, lean_object* v_targetNew_x3f_77_, lean_object* v_proofNew_x3f_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_75_, v_flippedNew_76_, v_targetNew_x3f_77_, v_proofNew_x3f_78_, v_a_79_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* v_e_91_, lean_object* v_flippedNew_92_, lean_object* v_targetNew_x3f_93_, lean_object* v_proofNew_x3f_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
uint8_t v_flippedNew_boxed_106_; lean_object* v_res_107_; 
v_flippedNew_boxed_106_ = lean_unbox(v_flippedNew_92_);
v_res_107_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(v_e_91_, v_flippedNew_boxed_106_, v_targetNew_x3f_93_, v_proofNew_x3f_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec(v_a_95_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* v_e_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = 0;
v___x_116_ = lean_box(0);
v___x_117_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_108_, v___x_115_, v___x_116_, v___x_116_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* v_e_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_126_, v_a_127_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* v_e_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(v_e_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec(v_a_140_);
return v_res_151_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* v_parent_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_Lean_Expr_isApp(v_parent_152_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_Expr_isArrow(v_parent_152_);
return v___x_154_;
}
else
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_isMatchCond(v_parent_152_);
if (v___x_155_ == 0)
{
return v___x_153_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_Expr_isArrow(v_parent_152_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_157_);
lean_dec_ref(v_parent_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_env_167_; uint8_t v___x_168_; lean_object* v_env_169_; lean_object* v___x_170_; lean_object* v_toCold_171_; lean_object* v_mctx_172_; lean_object* v_lctx_173_; lean_object* v_options_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
v___x_168_ = 0;
v_env_169_ = l_Lean_Environment_setRecordingDeps(v_env_167_, v___x_168_);
v___x_170_ = lean_st_ref_get(v___y_162_);
v_toCold_171_ = lean_ctor_get(v___y_163_, 0);
v_mctx_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc_ref(v_mctx_172_);
lean_dec(v___x_170_);
v_lctx_173_ = lean_ctor_get(v___y_161_, 2);
v_options_174_ = lean_ctor_get(v_toCold_171_, 2);
lean_inc_ref(v_options_174_);
lean_inc_ref(v_lctx_173_);
v___x_175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_175_, 0, v_env_169_);
lean_ctor_set(v___x_175_, 1, v_mctx_172_);
lean_ctor_set(v___x_175_, 2, v_lctx_173_);
lean_ctor_set(v___x_175_, 3, v_options_174_);
v___x_176_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_msgData_160_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_185_; double v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_float_of_nat(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_244_; 
v_ref_197_ = lean_ctor_get(v___y_194_, 2);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_244_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_244_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_244_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v_traceState_204_; lean_object* v_env_205_; lean_object* v_nextMacroScope_206_; lean_object* v_ngen_207_; lean_object* v_auxDeclNGen_208_; lean_object* v_cache_209_; lean_object* v_recordedDeps_210_; lean_object* v_messages_211_; lean_object* v_infoState_212_; lean_object* v_snapshotTasks_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_243_; 
v___x_203_ = lean_st_ref_take(v___y_195_);
v_traceState_204_ = lean_ctor_get(v___x_203_, 4);
v_env_205_ = lean_ctor_get(v___x_203_, 0);
v_nextMacroScope_206_ = lean_ctor_get(v___x_203_, 1);
v_ngen_207_ = lean_ctor_get(v___x_203_, 2);
v_auxDeclNGen_208_ = lean_ctor_get(v___x_203_, 3);
v_cache_209_ = lean_ctor_get(v___x_203_, 5);
v_recordedDeps_210_ = lean_ctor_get(v___x_203_, 6);
v_messages_211_ = lean_ctor_get(v___x_203_, 7);
v_infoState_212_ = lean_ctor_get(v___x_203_, 8);
v_snapshotTasks_213_ = lean_ctor_get(v___x_203_, 9);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_243_ == 0)
{
v___x_215_ = v___x_203_;
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snapshotTasks_213_);
lean_inc(v_infoState_212_);
lean_inc(v_messages_211_);
lean_inc(v_recordedDeps_210_);
lean_inc(v_cache_209_);
lean_inc(v_traceState_204_);
lean_inc(v_auxDeclNGen_208_);
lean_inc(v_ngen_207_);
lean_inc(v_nextMacroScope_206_);
lean_inc(v_env_205_);
lean_dec(v___x_203_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_243_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint64_t v_tid_217_; lean_object* v_traces_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_242_; 
v_tid_217_ = lean_ctor_get_uint64(v_traceState_204_, sizeof(void*)*1);
v_traces_218_ = lean_ctor_get(v_traceState_204_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_traceState_204_);
if (v_isSharedCheck_242_ == 0)
{
v___x_220_ = v_traceState_204_;
v_isShared_221_ = v_isSharedCheck_242_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_traces_218_);
lean_dec(v_traceState_204_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_242_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; double v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_box(0);
v___x_224_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_225_ = 0;
v___x_226_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_227_, 0, v_cls_190_);
lean_ctor_set(v___x_227_, 1, v___x_223_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3, v___x_224_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3 + 8, v___x_224_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*3 + 16, v___x_225_);
v___x_228_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_229_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v_a_199_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_inc(v_ref_197_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_ref_197_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_PersistentArray_push___redArg(v_traces_218_, v___x_230_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_231_);
v___x_233_ = v___x_220_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_231_);
lean_ctor_set_uint64(v_reuseFailAlloc_241_, sizeof(void*)*1, v_tid_217_);
v___x_233_ = v_reuseFailAlloc_241_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 4, v___x_233_);
v___x_235_ = v___x_215_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_env_205_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_nextMacroScope_206_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_ngen_207_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_auxDeclNGen_208_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 5, v_cache_209_);
lean_ctor_set(v_reuseFailAlloc_240_, 6, v_recordedDeps_210_);
lean_ctor_set(v_reuseFailAlloc_240_, 7, v_messages_211_);
lean_ctor_set(v_reuseFailAlloc_240_, 8, v_infoState_212_);
lean_ctor_set(v_reuseFailAlloc_240_, 9, v_snapshotTasks_213_);
v___x_235_ = v_reuseFailAlloc_240_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_st_ref_put(v___y_195_, v___x_235_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_222_);
v___x_238_ = v___x_201_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_222_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_245_, lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_245_, v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_253_, lean_object* v_xs_254_, lean_object* v_v_255_, lean_object* v_i_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_xs_254_);
v___x_258_ = lean_nat_dec_lt(v_i_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v_i_256_);
lean_dec_ref(v_v_255_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_fget_borrowed(v_xs_254_, v_i_256_);
lean_inc_ref(v_v_255_);
lean_inc(v___x_260_);
v___x_261_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_253_, v___x_260_, v_v_255_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_i_256_, v___x_262_);
lean_dec(v_i_256_);
v_i_256_ = v___x_263_;
goto _start;
}
else
{
lean_object* v___x_265_; 
lean_dec_ref(v_v_255_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_i_256_);
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_266_, lean_object* v_xs_267_, lean_object* v_v_268_, lean_object* v_i_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_266_, v_xs_267_, v_v_268_, v_i_269_);
lean_dec_ref(v_xs_267_);
lean_dec_ref(v___x_266_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_271_, lean_object* v_xs_272_, lean_object* v_v_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_271_, v_xs_272_, v_v_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_276_, lean_object* v_xs_277_, lean_object* v_v_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_276_, v_xs_277_, v_v_278_);
lean_dec_ref(v_xs_277_);
lean_dec_ref(v___x_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_280_, lean_object* v_x_281_, size_t v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_es_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v_j_288_; lean_object* v_entry_289_; 
v_es_284_ = lean_ctor_get(v_x_281_, 0);
v___x_285_ = lean_box(2);
v___x_286_ = ((size_t)31ULL);
v___x_287_ = lean_usize_land(v_x_282_, v___x_286_);
v_j_288_ = lean_usize_to_nat(v___x_287_);
v_entry_289_ = lean_array_get(v___x_285_, v_es_284_, v_j_288_);
switch(lean_obj_tag(v_entry_289_))
{
case 0:
{
lean_object* v_key_290_; uint8_t v___x_291_; 
v_key_290_ = lean_ctor_get(v_entry_289_, 0);
lean_inc(v_key_290_);
lean_dec_ref_known(v_entry_289_, 2);
v___x_291_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_280_, v_x_283_, v_key_290_);
if (v___x_291_ == 0)
{
lean_dec(v_j_288_);
return v_x_281_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
lean_inc_ref(v_es_284_);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_x_281_, 0);
lean_dec(v_unused_300_);
v___x_293_ = v_x_281_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_x_281_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_array_set(v_es_284_, v_j_288_, v___x_285_);
lean_dec(v_j_288_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_295_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
case 1:
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_335_; 
lean_inc_ref(v_es_284_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_x_281_, 0);
lean_dec(v_unused_336_);
v___x_302_ = v_x_281_;
v_isShared_303_ = v_isSharedCheck_335_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_x_281_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_335_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_node_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_334_; 
v_node_304_ = lean_ctor_get(v_entry_289_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_entry_289_);
if (v_isSharedCheck_334_ == 0)
{
v___x_306_ = v_entry_289_;
v_isShared_307_ = v_isSharedCheck_334_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_node_304_);
lean_dec(v_entry_289_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_334_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
size_t v___x_308_; lean_object* v_entries_309_; size_t v___x_310_; lean_object* v_newNode_311_; lean_object* v___x_312_; 
v___x_308_ = ((size_t)5ULL);
v_entries_309_ = lean_array_set(v_es_284_, v_j_288_, v___x_285_);
v___x_310_ = lean_usize_shift_right(v_x_282_, v___x_308_);
v_newNode_311_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_280_, v_node_304_, v___x_310_, v_x_283_);
lean_inc_ref(v_newNode_311_);
v___x_312_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_314_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_newNode_311_);
v___x_314_ = v___x_306_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_newNode_311_);
v___x_314_ = v_reuseFailAlloc_319_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_array_set(v_entries_309_, v_j_288_, v___x_314_);
lean_dec(v_j_288_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_315_);
v___x_317_ = v___x_302_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_val_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_newNode_311_);
lean_del_object(v___x_306_);
v_val_320_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_312_, 1);
v_fst_321_ = lean_ctor_get(v_val_320_, 0);
v_snd_322_ = lean_ctor_get(v_val_320_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_val_320_);
if (v_isSharedCheck_333_ == 0)
{
v___x_324_ = v_val_320_;
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_snd_322_);
lean_inc(v_fst_321_);
lean_dec(v_val_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_fst_321_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_snd_322_);
v___x_327_ = v_reuseFailAlloc_332_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_array_set(v_entries_309_, v_j_288_, v___x_327_);
lean_dec(v_j_288_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_328_);
v___x_330_ = v___x_302_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_288_);
lean_dec_ref(v_x_283_);
return v_x_281_;
}
}
}
else
{
lean_object* v_ks_337_; lean_object* v_vs_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_352_; 
v_ks_337_ = lean_ctor_get(v_x_281_, 0);
v_vs_338_ = lean_ctor_get(v_x_281_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_352_ == 0)
{
v___x_340_ = v_x_281_;
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_vs_338_);
lean_inc(v_ks_337_);
lean_dec(v_x_281_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; 
v___x_342_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_280_, v_ks_337_, v_x_283_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_344_; 
if (v_isShared_341_ == 0)
{
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_ks_337_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_vs_338_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
else
{
lean_object* v_val_346_; lean_object* v_keys_x27_347_; lean_object* v_vals_x27_348_; lean_object* v___x_350_; 
v_val_346_ = lean_ctor_get(v___x_342_, 0);
lean_inc_n(v_val_346_, 2);
lean_dec_ref_known(v___x_342_, 1);
v_keys_x27_347_ = l_Array_eraseIdx___redArg(v_ks_337_, v_val_346_);
v_vals_x27_348_ = l_Array_eraseIdx___redArg(v_vs_338_, v_val_346_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_vals_x27_348_);
lean_ctor_set(v___x_340_, 0, v_keys_x27_347_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_keys_x27_347_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_vals_x27_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
size_t v_x_22817__boxed_357_; lean_object* v_res_358_; 
v_x_22817__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_22817__boxed_357_, v_x_356_);
lean_dec_ref(v___x_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint64_t v___x_362_; size_t v_h_363_; lean_object* v___x_364_; 
lean_inc_ref(v_x_361_);
v___x_362_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_359_, v_x_361_);
v_h_363_ = lean_uint64_to_usize(v___x_362_);
v___x_364_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_359_, v_x_360_, v_h_363_, v_x_361_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_365_, v_x_366_, v_x_367_);
lean_dec_ref(v___x_365_);
return v_res_368_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_381_ = l_Lean_Name_append(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
if (lean_obj_tag(v_as_x27_385_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_386_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v___x_443_; 
v_head_399_ = lean_ctor_get(v_as_x27_385_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_385_, 1);
v___x_401_ = lean_box(0);
v___x_443_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_399_);
if (v___x_443_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v___x_445_; 
lean_inc(v_head_399_);
v___x_445_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_399_, v___y_387_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; uint8_t v___x_447_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v___x_447_ = lean_unbox(v_a_446_);
lean_dec(v_a_446_);
if (v___x_447_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_toCold_449_; lean_object* v_options_450_; uint8_t v_hasTrace_451_; 
v_toCold_449_ = lean_ctor_get(v___y_395_, 0);
v_options_450_ = lean_ctor_get(v_toCold_449_, 2);
v_hasTrace_451_ = lean_ctor_get_uint8(v_options_450_, sizeof(void*)*1);
if (v_hasTrace_451_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_inheritedTraceOptions_452_ = lean_ctor_get(v_toCold_449_, 11);
v___x_453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_454_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_452_, v_options_450_, v___x_454_);
if (v___x_455_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Grind_updateLastTag(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_457_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_458_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_453_, v___x_459_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_dec_ref_known(v___x_460_, 1);
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
return v___x_460_;
}
}
else
{
return v___x_456_;
}
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_445_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_445_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toGoalState_405_; lean_object* v_mvarId_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_442_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toGoalState_405_ = lean_ctor_get(v___x_404_, 0);
v_mvarId_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_442_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_442_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_mvarId_406_);
lean_inc(v_toGoalState_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_442_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_nextDeclIdx_410_; lean_object* v_enodeMap_411_; lean_object* v_exprs_412_; lean_object* v_parents_413_; lean_object* v_congrTable_414_; lean_object* v_appMap_415_; lean_object* v_indicesFound_416_; lean_object* v_toProcess_417_; lean_object* v_internalizing_418_; uint8_t v_inconsistent_419_; lean_object* v_nextIdx_420_; lean_object* v_newRawFacts_421_; lean_object* v_facts_422_; lean_object* v_extThms_423_; lean_object* v_ematch_424_; lean_object* v_inj_425_; lean_object* v_split_426_; lean_object* v_clean_427_; lean_object* v_sstates_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_441_; 
v_nextDeclIdx_410_ = lean_ctor_get(v_toGoalState_405_, 0);
v_enodeMap_411_ = lean_ctor_get(v_toGoalState_405_, 1);
v_exprs_412_ = lean_ctor_get(v_toGoalState_405_, 2);
v_parents_413_ = lean_ctor_get(v_toGoalState_405_, 3);
v_congrTable_414_ = lean_ctor_get(v_toGoalState_405_, 4);
v_appMap_415_ = lean_ctor_get(v_toGoalState_405_, 5);
v_indicesFound_416_ = lean_ctor_get(v_toGoalState_405_, 6);
v_toProcess_417_ = lean_ctor_get(v_toGoalState_405_, 7);
v_internalizing_418_ = lean_ctor_get(v_toGoalState_405_, 8);
v_inconsistent_419_ = lean_ctor_get_uint8(v_toGoalState_405_, sizeof(void*)*18);
v_nextIdx_420_ = lean_ctor_get(v_toGoalState_405_, 9);
v_newRawFacts_421_ = lean_ctor_get(v_toGoalState_405_, 10);
v_facts_422_ = lean_ctor_get(v_toGoalState_405_, 11);
v_extThms_423_ = lean_ctor_get(v_toGoalState_405_, 12);
v_ematch_424_ = lean_ctor_get(v_toGoalState_405_, 13);
v_inj_425_ = lean_ctor_get(v_toGoalState_405_, 14);
v_split_426_ = lean_ctor_get(v_toGoalState_405_, 15);
v_clean_427_ = lean_ctor_get(v_toGoalState_405_, 16);
v_sstates_428_ = lean_ctor_get(v_toGoalState_405_, 17);
v_isSharedCheck_441_ = !lean_is_exclusive(v_toGoalState_405_);
if (v_isSharedCheck_441_ == 0)
{
v___x_430_ = v_toGoalState_405_;
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_sstates_428_);
lean_inc(v_clean_427_);
lean_inc(v_split_426_);
lean_inc(v_inj_425_);
lean_inc(v_ematch_424_);
lean_inc(v_extThms_423_);
lean_inc(v_facts_422_);
lean_inc(v_newRawFacts_421_);
lean_inc(v_nextIdx_420_);
lean_inc(v_internalizing_418_);
lean_inc(v_toProcess_417_);
lean_inc(v_indicesFound_416_);
lean_inc(v_appMap_415_);
lean_inc(v_congrTable_414_);
lean_inc(v_parents_413_);
lean_inc(v_exprs_412_);
lean_inc(v_enodeMap_411_);
lean_inc(v_nextDeclIdx_410_);
lean_dec(v_toGoalState_405_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_head_399_);
v___x_432_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_411_, v_congrTable_414_, v_head_399_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_nextDeclIdx_410_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_enodeMap_411_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_exprs_412_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_parents_413_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_appMap_415_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_indicesFound_416_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_toProcess_417_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_internalizing_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_nextIdx_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 10, v_newRawFacts_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 11, v_facts_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 12, v_extThms_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 13, v_ematch_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 14, v_inj_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 15, v_split_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 16, v_clean_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 17, v_sstates_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_440_, sizeof(void*)*18, v_inconsistent_419_);
v___x_434_ = v_reuseFailAlloc_440_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_434_);
v___x_436_ = v___x_408_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_mvarId_406_);
v___x_436_ = v_reuseFailAlloc_439_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_st_ref_put(v___y_403_, v___x_436_);
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_469_, lean_object* v_b_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_469_, v_b_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v___y_471_);
lean_dec(v_as_x27_469_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_Grind_getParents___redArg(v_root_483_, v_a_484_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_496_);
v___x_498_ = lean_box(0);
v___x_499_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_497_, v___x_498_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v___x_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v___x_499_, 0);
lean_dec(v_unused_507_);
v___x_501_ = v___x_499_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_dec(v___x_499_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_a_496_);
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_496_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_496_);
v_a_508_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_499_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_499_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_root_516_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_529_, lean_object* v_00_u03b2_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_529_, v_x_531_, v_x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_534_, lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_534_, v_00_u03b2_535_, v_x_536_, v_x_537_);
lean_dec_ref(v___x_534_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_539_, v_msg_540_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_553_, v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_567_, lean_object* v_as_x27_568_, lean_object* v_b_569_, lean_object* v_a_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_568_, v_b_569_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_583_, lean_object* v_as_x27_584_, lean_object* v_b_585_, lean_object* v_a_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_583_, v_as_x27_584_, v_b_585_, v_a_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v_as_x27_584_);
lean_dec(v_as_583_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_599_, lean_object* v_00_u03b2_600_, lean_object* v_x_601_, size_t v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_599_, v_x_601_, v_x_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_605_, lean_object* v_00_u03b2_606_, lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
size_t v_x_23277__boxed_610_; lean_object* v_res_611_; 
v_x_23277__boxed_610_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_res_611_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_605_, v_00_u03b2_606_, v_x_607_, v_x_23277__boxed_610_, v_x_609_);
lean_dec_ref(v___x_605_);
return v_res_611_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
if (lean_obj_tag(v_as_x27_615_) == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_616_);
return v___x_628_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v___x_645_; 
v_head_629_ = lean_ctor_get(v_as_x27_615_, 0);
v_tail_630_ = lean_ctor_get(v_as_x27_615_, 1);
v___x_631_ = lean_box(0);
v___x_645_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_629_);
if (v___x_645_ == 0)
{
v_as_x27_615_ = v_tail_630_;
v_b_616_ = v___x_631_;
goto _start;
}
else
{
lean_object* v___x_647_; 
lean_inc(v_head_629_);
v___x_647_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_629_, v___y_617_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; uint8_t v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = lean_unbox(v_a_648_);
lean_dec(v_a_648_);
if (v___x_649_ == 0)
{
v_as_x27_615_ = v_tail_630_;
v_b_616_ = v___x_631_;
goto _start;
}
else
{
lean_object* v_toCold_651_; lean_object* v_options_652_; uint8_t v_hasTrace_653_; 
v_toCold_651_ = lean_ctor_get(v___y_625_, 0);
v_options_652_ = lean_ctor_get(v_toCold_651_, 2);
v_hasTrace_653_ = lean_ctor_get_uint8(v_options_652_, sizeof(void*)*1);
if (v_hasTrace_653_ == 0)
{
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
goto v___jp_632_;
}
else
{
lean_object* v_inheritedTraceOptions_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_inheritedTraceOptions_654_ = lean_ctor_get(v_toCold_651_, 11);
v___x_655_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_656_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_657_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_654_, v_options_652_, v___x_656_);
if (v___x_657_ == 0)
{
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
goto v___jp_632_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Grind_updateLastTag(v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref_known(v___x_658_, 1);
v___x_659_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_629_);
v___x_660_ = l_Lean_MessageData_ofExpr(v_head_629_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_655_, v___x_661_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
goto v___jp_632_;
}
else
{
return v___x_662_;
}
}
else
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_647_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_647_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
v___jp_632_:
{
lean_object* v___x_643_; 
lean_inc(v_head_629_);
v___x_643_ = l_Lean_Meta_Grind_addCongrTable(v_head_629_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref_known(v___x_643_, 1);
v_as_x27_615_ = v_tail_630_;
v_b_616_ = v___x_631_;
goto _start;
}
else
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_671_, v_b_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v_as_x27_671_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_685_);
v___x_698_ = lean_box(0);
v___x_699_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_697_, v___x_698_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v___x_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_699_, 0);
lean_dec(v_unused_707_);
v___x_701_ = v___x_699_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_dec(v___x_699_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_698_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_698_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec(v_a_709_);
lean_dec(v_parents_708_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_721_, lean_object* v_as_x27_722_, lean_object* v_b_723_, lean_object* v_a_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_722_, v_b_723_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_737_, lean_object* v_as_x27_738_, lean_object* v_b_739_, lean_object* v_a_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_737_, v_as_x27_738_, v_b_739_, v_a_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v_as_x27_738_);
lean_dec(v_as_737_);
return v_res_752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_753_, lean_object* v_i_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_get_size(v_keys_753_);
v___x_757_ = lean_nat_dec_lt(v_i_754_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v_i_754_);
return v___x_757_;
}
else
{
lean_object* v_k_x27_758_; uint8_t v___x_759_; 
v_k_x27_758_ = lean_array_fget_borrowed(v_keys_753_, v_i_754_);
v___x_759_ = l_Lean_instBEqMVarId_beq(v_k_755_, v_k_x27_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_nat_add(v_i_754_, v___x_760_);
lean_dec(v_i_754_);
v_i_754_ = v___x_761_;
goto _start;
}
else
{
lean_dec(v_i_754_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_763_, lean_object* v_i_764_, lean_object* v_k_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_763_, v_i_764_, v_k_765_);
lean_dec(v_k_765_);
lean_dec_ref(v_keys_763_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_768_, size_t v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v_es_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v_j_775_; lean_object* v___x_776_; 
v_es_771_ = lean_ctor_get(v_x_768_, 0);
v___x_772_ = lean_box(2);
v___x_773_ = ((size_t)31ULL);
v___x_774_ = lean_usize_land(v_x_769_, v___x_773_);
v_j_775_ = lean_usize_to_nat(v___x_774_);
v___x_776_ = lean_array_get_borrowed(v___x_772_, v_es_771_, v_j_775_);
lean_dec(v_j_775_);
switch(lean_obj_tag(v___x_776_))
{
case 0:
{
lean_object* v_key_777_; uint8_t v___x_778_; 
v_key_777_ = lean_ctor_get(v___x_776_, 0);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_770_, v_key_777_);
return v___x_778_;
}
case 1:
{
lean_object* v_node_779_; size_t v___x_780_; size_t v___x_781_; 
v_node_779_ = lean_ctor_get(v___x_776_, 0);
v___x_780_ = ((size_t)5ULL);
v___x_781_ = lean_usize_shift_right(v_x_769_, v___x_780_);
v_x_768_ = v_node_779_;
v_x_769_ = v___x_781_;
goto _start;
}
default: 
{
uint8_t v___x_783_; 
v___x_783_ = 0;
return v___x_783_;
}
}
}
else
{
lean_object* v_ks_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_ks_784_ = lean_ctor_get(v_x_768_, 0);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_784_, v___x_785_, v_x_770_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
size_t v_x_9681__boxed_790_; uint8_t v_res_791_; lean_object* v_r_792_; 
v_x_9681__boxed_790_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_791_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_787_, v_x_9681__boxed_790_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_x_787_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
uint64_t v___x_795_; size_t v___x_796_; uint8_t v___x_797_; 
v___x_795_ = l_Lean_instHashableMVarId_hash(v_x_794_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_793_, v___x_796_, v_x_794_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_798_, v_x_799_);
lean_dec(v_x_799_);
lean_dec_ref(v_x_798_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; lean_object* v_mctx_806_; lean_object* v_eAssignment_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = lean_st_ref_get(v___y_803_);
v_mctx_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc_ref(v_mctx_806_);
lean_dec(v___x_805_);
v_eAssignment_807_ = lean_ctor_get(v_mctx_806_, 8);
lean_inc_ref(v_eAssignment_807_);
lean_dec_ref(v_mctx_806_);
v___x_808_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_807_, v_mvarId_802_);
lean_dec_ref(v_eAssignment_807_);
v___x_809_ = lean_box(v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec(v_mvarId_811_);
return v_res_814_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_box(0);
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_833_ = l_Lean_mkConst(v___x_832_, v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_mvarId_846_; lean_object* v___x_847_; lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_901_; 
v___x_845_ = lean_st_ref_get(v_a_834_);
v_mvarId_846_ = lean_ctor_get(v___x_845_, 1);
lean_inc(v_mvarId_846_);
lean_dec(v___x_845_);
v___x_847_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_846_, v_a_841_);
lean_dec(v_mvarId_846_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_901_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_901_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_901_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
lean_del_object(v___x_850_);
v___x_853_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_838_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_854_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_838_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_838_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_863_ = l_Lean_mkApp4(v___x_861_, v_a_858_, v_a_860_, v_a_856_, v___x_862_);
v___x_864_ = l_Lean_Meta_Grind_closeGoal(v___x_863_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
return v___x_864_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_a_858_);
lean_dec(v_a_856_);
v_a_865_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_859_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_859_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_856_);
v_a_873_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_857_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_857_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_855_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_855_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_853_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_853_);
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
else
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_897_);
v___x_899_ = v___x_850_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec(v_a_902_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_914_, v___y_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v_mvarId_927_);
return v_res_939_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
uint8_t v_res_947_; lean_object* v_r_948_; 
v_res_947_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_944_, v_x_945_, v_x_946_);
lean_dec(v_x_946_);
lean_dec_ref(v_x_945_);
v_r_948_ = lean_box(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, size_t v_x_951_, lean_object* v_x_952_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_950_, v_x_951_, v_x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
size_t v_x_9964__boxed_958_; uint8_t v_res_959_; lean_object* v_r_960_; 
v_x_9964__boxed_958_ = lean_unbox_usize(v_x_956_);
lean_dec(v_x_956_);
v_res_959_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_954_, v_x_955_, v_x_9964__boxed_958_, v_x_957_);
lean_dec(v_x_957_);
lean_dec_ref(v_x_955_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_heq_964_, lean_object* v_i_965_, lean_object* v_k_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_962_, v_i_965_, v_k_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_968_, lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_heq_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
uint8_t v_res_974_; lean_object* v_r_975_; 
v_res_974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_968_, v_keys_969_, v_vals_970_, v_heq_971_, v_i_972_, v_k_973_);
lean_dec(v_k_973_);
lean_dec_ref(v_vals_970_);
lean_dec_ref(v_keys_969_);
v_r_975_ = lean_box(v_res_974_);
return v_r_975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_box(0);
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_981_ = l_Lean_mkConst(v___x_980_, v___x_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_982_, lean_object* v_rhs_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; 
lean_inc_ref(v_rhs_983_);
lean_inc_ref(v_lhs_982_);
v___x_995_ = l_Lean_Meta_mkEq(v_lhs_982_, v_rhs_983_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
lean_inc(v_a_993_);
lean_inc_ref(v_a_992_);
lean_inc(v_a_991_);
lean_inc_ref(v_a_990_);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc(v_a_984_);
v___x_997_ = lean_grind_mk_eq_proof(v_lhs_982_, v_rhs_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
lean_inc(v_a_996_);
v___x_999_ = l_Lean_Meta_mkDecide(v_a_996_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1002_ = l_Lean_Expr_appArg_x21(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1003_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_996_);
v___x_1004_ = l_Lean_mkApp3(v___x_1001_, v_a_996_, v___x_1002_, v___x_1003_);
v___x_1005_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_988_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1008_ = l_Lean_mkApp4(v___x_1007_, v_a_996_, v_a_1006_, v___x_1004_, v_a_998_);
v___x_1009_ = l_Lean_Meta_Grind_closeGoal(v___x_1008_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___x_1004_);
lean_dec(v_a_998_);
lean_dec(v_a_996_);
v_a_1010_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1005_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1005_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_998_);
lean_dec(v_a_996_);
v_a_1018_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_999_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_999_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_a_996_);
v_a_1026_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_997_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_997_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_rhs_983_);
lean_dec_ref(v_lhs_982_);
v_a_1034_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_995_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_995_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1042_, lean_object* v_rhs_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1042_, v_rhs_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec(v_a_1044_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1056_, lean_object* v_as_x27_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
if (lean_obj_tag(v_as_x27_1057_) == 0)
{
lean_object* v___x_1070_; 
lean_dec(v___x_1056_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_b_1058_);
return v___x_1070_;
}
else
{
lean_object* v_head_1071_; lean_object* v_tail_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_head_1071_ = lean_ctor_get(v_as_x27_1057_, 0);
v_tail_1072_ = lean_ctor_get(v_as_x27_1057_, 1);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_st_ref_get(v___y_1059_);
lean_inc(v_head_1071_);
v___x_1075_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1074_, v_head_1071_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v_self_1077_; lean_object* v_next_1078_; lean_object* v_root_1079_; lean_object* v_congr_1080_; lean_object* v_target_x3f_1081_; lean_object* v_proof_x3f_1082_; uint8_t v_flipped_1083_; lean_object* v_size_1084_; uint8_t v_interpreted_1085_; uint8_t v_ctor_1086_; uint8_t v_hasLambdas_1087_; uint8_t v_heqProofs_1088_; lean_object* v_idx_1089_; lean_object* v_generation_1090_; lean_object* v_mt_1091_; lean_object* v_sTerms_1092_; uint8_t v_funCC_1093_; lean_object* v_ematchDiagSource_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1106_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v_self_1077_ = lean_ctor_get(v_a_1076_, 0);
v_next_1078_ = lean_ctor_get(v_a_1076_, 1);
v_root_1079_ = lean_ctor_get(v_a_1076_, 2);
v_congr_1080_ = lean_ctor_get(v_a_1076_, 3);
v_target_x3f_1081_ = lean_ctor_get(v_a_1076_, 4);
v_proof_x3f_1082_ = lean_ctor_get(v_a_1076_, 5);
v_flipped_1083_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12);
v_size_1084_ = lean_ctor_get(v_a_1076_, 6);
v_interpreted_1085_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12 + 1);
v_ctor_1086_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12 + 2);
v_hasLambdas_1087_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12 + 3);
v_heqProofs_1088_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12 + 4);
v_idx_1089_ = lean_ctor_get(v_a_1076_, 7);
v_generation_1090_ = lean_ctor_get(v_a_1076_, 8);
v_mt_1091_ = lean_ctor_get(v_a_1076_, 9);
v_sTerms_1092_ = lean_ctor_get(v_a_1076_, 10);
v_funCC_1093_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1094_ = lean_ctor_get(v_a_1076_, 11);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1096_ = v_a_1076_;
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_ematchDiagSource_1094_);
lean_inc(v_sTerms_1092_);
lean_inc(v_mt_1091_);
lean_inc(v_generation_1090_);
lean_inc(v_idx_1089_);
lean_inc(v_size_1084_);
lean_inc(v_proof_x3f_1082_);
lean_inc(v_target_x3f_1081_);
lean_inc(v_congr_1080_);
lean_inc(v_root_1079_);
lean_inc(v_next_1078_);
lean_inc(v_self_1077_);
lean_dec(v_a_1076_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1106_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_lt(v_mt_1091_, v___x_1056_);
lean_dec(v_mt_1091_);
if (v___x_1098_ == 0)
{
lean_del_object(v___x_1096_);
lean_dec(v_ematchDiagSource_1094_);
lean_dec(v_sTerms_1092_);
lean_dec(v_generation_1090_);
lean_dec(v_idx_1089_);
lean_dec(v_size_1084_);
lean_dec(v_proof_x3f_1082_);
lean_dec(v_target_x3f_1081_);
lean_dec_ref(v_congr_1080_);
lean_dec_ref(v_root_1079_);
lean_dec_ref(v_next_1078_);
lean_dec_ref(v_self_1077_);
v_as_x27_1057_ = v_tail_1072_;
v_b_1058_ = v___x_1073_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
lean_inc(v___x_1056_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 9, v___x_1056_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_self_1077_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_next_1078_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_root_1079_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_congr_1080_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_target_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_proof_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1105_, 6, v_size_1084_);
lean_ctor_set(v_reuseFailAlloc_1105_, 7, v_idx_1089_);
lean_ctor_set(v_reuseFailAlloc_1105_, 8, v_generation_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 9, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1105_, 10, v_sTerms_1092_);
lean_ctor_set(v_reuseFailAlloc_1105_, 11, v_ematchDiagSource_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12, v_flipped_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 1, v_interpreted_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 2, v_ctor_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 3, v_hasLambdas_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 4, v_heqProofs_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 5, v_funCC_1093_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; 
lean_inc(v_head_1071_);
v___x_1102_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1071_, v___x_1101_, v___y_1059_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1071_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
v_as_x27_1057_ = v_tail_1072_;
v_b_1058_ = v___x_1073_;
goto _start;
}
else
{
lean_dec(v___x_1056_);
return v___x_1103_;
}
}
else
{
lean_dec(v___x_1056_);
return v___x_1102_;
}
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v___x_1056_);
v_a_1107_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1075_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1075_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_toGoalState_1128_; lean_object* v_ematch_1129_; lean_object* v_gmt_1130_; lean_object* v___x_1131_; 
v___x_1127_ = lean_st_ref_get(v_a_1116_);
v_toGoalState_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_toGoalState_1128_);
lean_dec(v___x_1127_);
v_ematch_1129_ = lean_ctor_get(v_toGoalState_1128_, 13);
lean_inc_ref(v_ematch_1129_);
lean_dec_ref(v_toGoalState_1128_);
v_gmt_1130_ = lean_ctor_get(v_ematch_1129_, 1);
lean_inc(v_gmt_1130_);
lean_dec_ref(v_ematch_1129_);
v___x_1131_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1132_);
lean_dec(v_a_1132_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1130_, v___x_1133_, v___x_1134_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v___x_1133_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1143_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
return v___x_1135_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_gmt_1130_);
v_a_1144_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1131_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1131_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_root_1152_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1165_, lean_object* v_as_x27_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1165_, v_as_x27_1166_, v_b_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v_as_x27_1166_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1180_, lean_object* v_as_1181_, lean_object* v_as_x27_1182_, lean_object* v_b_1183_, lean_object* v_a_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1180_, v_as_x27_1182_, v_b_1183_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1197_, lean_object* v_as_1198_, lean_object* v_as_x27_1199_, lean_object* v_b_1200_, lean_object* v_a_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1197_, v_as_1198_, v_as_x27_1199_, v_b_1200_, v_a_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec(v_as_x27_1199_);
lean_dec(v_as_1198_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
if (lean_obj_tag(v_a_1214_) == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = l_List_reverse___redArg(v_a_1215_);
return v___x_1216_;
}
else
{
lean_object* v_head_1217_; lean_object* v_tail_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1227_; 
v_head_1217_ = lean_ctor_get(v_a_1214_, 0);
v_tail_1218_ = lean_ctor_get(v_a_1214_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_a_1214_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1220_ = v_a_1214_;
v_isShared_1221_ = v_isSharedCheck_1227_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_tail_1218_);
lean_inc(v_head_1217_);
lean_dec(v_a_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1227_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_MessageData_ofExpr(v_head_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v_a_1215_);
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1215_);
v___x_1224_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
v_a_1214_ = v_tail_1218_;
v_a_1215_ = v___x_1224_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1228_, lean_object* v_a_1229_, lean_object* v_fst_1230_, lean_object* v_a_1231_, lean_object* v_lams_1232_, lean_object* v_____r_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1228_, v_a_1231_, v___y_1234_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; uint8_t v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = lean_unbox(v_a_1283_);
lean_dec(v_a_1283_);
if (v___x_1284_ == 0)
{
goto v___jp_1245_;
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_inc(v_fst_1230_);
v___x_1285_ = l_Array_reverse___redArg(v_fst_1230_);
lean_inc(v_snd_1228_);
v___x_1286_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1232_, v_snd_1228_, v___x_1285_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_dec_ref_known(v___x_1286_, 1);
goto v___jp_1245_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_fst_1230_);
lean_dec(v_snd_1228_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_fst_1230_);
lean_dec(v_snd_1228_);
v_a_1295_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1282_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1282_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
v___jp_1245_:
{
if (lean_obj_tag(v_snd_1228_) == 5)
{
lean_object* v_fn_1246_; lean_object* v_arg_1247_; lean_object* v___x_1248_; 
v_fn_1246_ = lean_ctor_get(v_snd_1228_, 0);
lean_inc_ref(v_fn_1246_);
v_arg_1247_ = lean_ctor_get(v_snd_1228_, 1);
lean_inc_ref(v_arg_1247_);
v___x_1248_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1229_, v___y_1234_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = lean_box(0);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc(v___y_1234_);
v___x_1251_ = lean_grind_internalize(v_snd_1228_, v_a_1249_, v___x_1250_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1261_; 
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1262_);
v___x_1253_ = v___x_1251_;
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1251_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1255_ = lean_array_push(v_fst_1230_, v_arg_1247_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
lean_ctor_set(v___x_1256_, 1, v_fn_1246_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1257_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_fn_1246_);
lean_dec(v_fst_1230_);
v_a_1263_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1251_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1251_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_fn_1246_);
lean_dec_ref_known(v_snd_1228_, 2);
lean_dec(v_fst_1230_);
v_a_1271_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1248_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1248_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
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
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_fst_1230_);
lean_ctor_set(v___x_1279_, 1, v_snd_1228_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1303_ = _args[0];
lean_object* v_a_1304_ = _args[1];
lean_object* v_fst_1305_ = _args[2];
lean_object* v_a_1306_ = _args[3];
lean_object* v_lams_1307_ = _args[4];
lean_object* v_____r_1308_ = _args[5];
lean_object* v___y_1309_ = _args[6];
lean_object* v___y_1310_ = _args[7];
lean_object* v___y_1311_ = _args[8];
lean_object* v___y_1312_ = _args[9];
lean_object* v___y_1313_ = _args[10];
lean_object* v___y_1314_ = _args[11];
lean_object* v___y_1315_ = _args[12];
lean_object* v___y_1316_ = _args[13];
lean_object* v___y_1317_ = _args[14];
lean_object* v___y_1318_ = _args[15];
lean_object* v___y_1319_ = _args[16];
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1303_, v_a_1304_, v_fst_1305_, v_a_1306_, v_lams_1307_, v_____r_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v_lams_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_a_1304_);
return v_res_1320_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1327_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1328_ = l_Lean_Name_append(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_lams_1334_, lean_object* v_a_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___y_1348_; lean_object* v_toCold_1368_; lean_object* v_options_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1408_; 
v_toCold_1368_ = lean_ctor_get(v___y_1344_, 0);
v_options_1369_ = lean_ctor_get(v_toCold_1368_, 2);
v_fst_1370_ = lean_ctor_get(v_a_1335_, 0);
v_snd_1371_ = lean_ctor_get(v_a_1335_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1335_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1373_ = v_a_1335_;
v_isShared_1374_ = v_isSharedCheck_1408_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_a_1335_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1408_;
goto v_resetjp_1372_;
}
v___jp_1347_:
{
if (lean_obj_tag(v___y_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_a_1349_ = lean_ctor_get(v___y_1348_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___y_1348_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v___y_1348_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___y_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
if (lean_obj_tag(v_a_1349_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v_a_1349_, 1);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_a_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v_a_1357_; 
lean_del_object(v___x_1351_);
v_a_1357_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v_a_1349_, 1);
v_a_1335_ = v_a_1357_;
goto _start;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___y_1348_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___y_1348_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___y_1348_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___y_1348_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
v_resetjp_1372_:
{
lean_object* v_inheritedTraceOptions_1375_; uint8_t v_hasTrace_1376_; 
v_inheritedTraceOptions_1375_ = lean_ctor_get(v_toCold_1368_, 11);
v_hasTrace_1376_ = lean_ctor_get_uint8(v_options_1369_, sizeof(void*)*1);
if (v_hasTrace_1376_ == 0)
{
lean_del_object(v___x_1373_);
goto v___jp_1377_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1380_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1381_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1375_, v_options_1369_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_del_object(v___x_1373_);
goto v___jp_1377_;
}
else
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Meta_Grind_updateLastTag(v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1383_, 1);
v___x_1384_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1371_);
v___x_1385_ = l_Lean_MessageData_ofExpr(v_snd_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 7);
lean_ctor_set(v___x_1373_, 1, v___x_1385_);
lean_ctor_set(v___x_1373_, 0, v___x_1384_);
v___x_1387_ = v___x_1373_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1380_, v___x_1387_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1371_, v_a_1332_, v_fst_1370_, v_a_1333_, v_lams_1334_, v_a_1389_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
v___y_1348_ = v___x_1390_;
goto v___jp_1347_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
v_a_1391_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1388_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1388_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1373_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
v_a_1400_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1383_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1383_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
v___jp_1377_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1371_, v_a_1332_, v_fst_1370_, v_a_1333_, v_lams_1334_, v___x_1378_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
v___y_1348_ = v___x_1379_;
goto v___jp_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_lams_1411_, lean_object* v_a_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1409_, v_a_1410_, v_lams_1411_, v_a_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v_lams_1411_);
lean_dec_ref(v_a_1410_);
lean_dec_ref(v_a_1409_);
return v_res_1424_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1430_, lean_object* v_lams_1431_, lean_object* v_as_x27_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
if (lean_obj_tag(v_as_x27_1432_) == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_b_1433_);
return v___x_1445_;
}
else
{
lean_object* v_toCold_1446_; lean_object* v_options_1447_; lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v_inheritedTraceOptions_1450_; uint8_t v_hasTrace_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; 
v_toCold_1446_ = lean_ctor_get(v___y_1442_, 0);
v_options_1447_ = lean_ctor_get(v_toCold_1446_, 2);
v_head_1448_ = lean_ctor_get(v_as_x27_1432_, 0);
v_tail_1449_ = lean_ctor_get(v_as_x27_1432_, 1);
v_inheritedTraceOptions_1450_ = lean_ctor_get(v_toCold_1446_, 11);
v_hasTrace_1451_ = lean_ctor_get_uint8(v_options_1447_, sizeof(void*)*1);
v___x_1452_ = lean_box(0);
v___x_1453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1451_ == 0)
{
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1477_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1450_, v_options_1447_, v___x_1477_);
if (v___x_1478_ == 0)
{
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_Grind_updateLastTag(v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref_known(v___x_1479_, 1);
v___x_1480_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1448_);
v___x_1481_ = l_Lean_MessageData_ofExpr(v_head_1448_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1476_, v___x_1482_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref_known(v___x_1483_, 1);
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
goto v___jp_1454_;
}
else
{
return v___x_1483_;
}
}
else
{
return v___x_1479_;
}
}
}
v___jp_1454_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_inc(v_head_1448_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1453_);
lean_ctor_set(v___x_1465_, 1, v_head_1448_);
v___x_1466_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1448_, v_a_1430_, v_lams_1431_, v___x_1465_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_dec_ref_known(v___x_1466_, 1);
v_as_x27_1432_ = v_tail_1449_;
v_b_1433_ = v___x_1452_;
goto _start;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1466_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1466_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1484_, lean_object* v_lams_1485_, lean_object* v_as_x27_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1484_, v_lams_1485_, v_as_x27_1486_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v_as_x27_1486_);
lean_dec_ref(v_lams_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1500_, lean_object* v_lams_1501_, lean_object* v_as_1502_, lean_object* v_as_x27_1503_, lean_object* v_b_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
if (lean_obj_tag(v_as_x27_1503_) == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1504_);
return v___x_1516_;
}
else
{
lean_object* v_toCold_1517_; lean_object* v_options_1518_; lean_object* v_head_1519_; lean_object* v_tail_1520_; lean_object* v_inheritedTraceOptions_1521_; uint8_t v_hasTrace_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; 
v_toCold_1517_ = lean_ctor_get(v___y_1513_, 0);
v_options_1518_ = lean_ctor_get(v_toCold_1517_, 2);
v_head_1519_ = lean_ctor_get(v_as_x27_1503_, 0);
v_tail_1520_ = lean_ctor_get(v_as_x27_1503_, 1);
v_inheritedTraceOptions_1521_ = lean_ctor_get(v_toCold_1517_, 11);
v_hasTrace_1522_ = lean_ctor_get_uint8(v_options_1518_, sizeof(void*)*1);
v___x_1523_ = lean_box(0);
v___x_1524_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1522_ == 0)
{
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1547_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1548_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1521_, v_options_1518_, v___x_1548_);
if (v___x_1549_ == 0)
{
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Meta_Grind_updateLastTag(v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref_known(v___x_1550_, 1);
v___x_1551_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1519_);
v___x_1552_ = l_Lean_MessageData_ofExpr(v_head_1519_);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1547_, v___x_1553_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref_known(v___x_1554_, 1);
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
goto v___jp_1525_;
}
else
{
return v___x_1554_;
}
}
else
{
return v___x_1550_;
}
}
}
v___jp_1525_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_inc(v_head_1519_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1524_);
lean_ctor_set(v___x_1536_, 1, v_head_1519_);
v___x_1537_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1519_, v_a_1500_, v_lams_1501_, v___x_1536_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref_known(v___x_1537_, 1);
v___x_1538_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1500_, v_lams_1501_, v_tail_1520_, v___x_1523_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1538_;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
v_a_1539_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1555_, lean_object* v_lams_1556_, lean_object* v_as_1557_, lean_object* v_as_x27_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1555_, v_lams_1556_, v_as_1557_, v_as_x27_1558_, v_b_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec(v_as_x27_1558_);
lean_dec(v_as_1557_);
lean_dec_ref(v_lams_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1578_, lean_object* v_lams_1579_, lean_object* v_as_1580_, size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_b_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_b_1583_);
return v___x_1596_;
}
else
{
lean_object* v_toCold_1597_; lean_object* v_options_1598_; lean_object* v_inheritedTraceOptions_1599_; uint8_t v_hasTrace_1600_; lean_object* v___x_1601_; lean_object* v_a_1602_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; 
v_toCold_1597_ = lean_ctor_get(v___y_1592_, 0);
v_options_1598_ = lean_ctor_get(v_toCold_1597_, 2);
v_inheritedTraceOptions_1599_ = lean_ctor_get(v_toCold_1597_, 11);
v_hasTrace_1600_ = lean_ctor_get_uint8(v_options_1598_, sizeof(void*)*1);
v___x_1601_ = lean_box(0);
v_a_1602_ = lean_array_uget_borrowed(v_as_1580_, v_i_1582_);
if (v_hasTrace_1600_ == 0)
{
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1629_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1630_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1599_, v_options_1598_, v___x_1630_);
if (v___x_1631_ == 0)
{
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
goto v___jp_1603_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_Grind_updateLastTag(v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref_known(v___x_1632_, 1);
v___x_1633_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1602_, v___y_1584_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1602_);
v___x_1636_ = l_Lean_MessageData_ofExpr(v_a_1602_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1634_);
lean_dec(v_a_1634_);
v___x_1641_ = lean_box(0);
v___x_1642_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1640_, v___x_1641_);
v___x_1643_ = l_Lean_MessageData_ofList(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1629_, v___x_1644_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_dec_ref_known(v___x_1645_, 1);
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
goto v___jp_1603_;
}
else
{
return v___x_1645_;
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1633_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1633_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
return v___x_1632_;
}
}
}
v___jp_1603_:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1602_, v___y_1604_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1615_);
lean_dec(v_a_1615_);
v___x_1617_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1578_, v_lams_1579_, v___x_1616_, v___x_1616_, v___x_1601_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___x_1616_);
if (lean_obj_tag(v___x_1617_) == 0)
{
size_t v___x_1618_; size_t v___x_1619_; 
lean_dec_ref_known(v___x_1617_, 1);
v___x_1618_ = ((size_t)1ULL);
v___x_1619_ = lean_usize_add(v_i_1582_, v___x_1618_);
v_i_1582_ = v___x_1619_;
v_b_1583_ = v___x_1601_;
goto _start;
}
else
{
return v___x_1617_;
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1614_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1614_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1654_ = _args[0];
lean_object* v_lams_1655_ = _args[1];
lean_object* v_as_1656_ = _args[2];
lean_object* v_sz_1657_ = _args[3];
lean_object* v_i_1658_ = _args[4];
lean_object* v_b_1659_ = _args[5];
lean_object* v___y_1660_ = _args[6];
lean_object* v___y_1661_ = _args[7];
lean_object* v___y_1662_ = _args[8];
lean_object* v___y_1663_ = _args[9];
lean_object* v___y_1664_ = _args[10];
lean_object* v___y_1665_ = _args[11];
lean_object* v___y_1666_ = _args[12];
lean_object* v___y_1667_ = _args[13];
lean_object* v___y_1668_ = _args[14];
lean_object* v___y_1669_ = _args[15];
lean_object* v___y_1670_ = _args[16];
_start:
{
size_t v_sz_boxed_1671_; size_t v_i_boxed_1672_; lean_object* v_res_1673_; 
v_sz_boxed_1671_ = lean_unbox_usize(v_sz_1657_);
lean_dec(v_sz_1657_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1654_, v_lams_1655_, v_as_1656_, v_sz_boxed_1671_, v_i_boxed_1672_, v_b_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v_as_1656_);
lean_dec_ref(v_lams_1655_);
lean_dec_ref(v_a_1654_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1674_, lean_object* v_lams_1675_, lean_object* v_as_1676_, size_t v_sz_1677_, size_t v_i_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v___x_1691_; 
v___x_1691_ = lean_usize_dec_lt(v_i_1678_, v_sz_1677_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_b_1679_);
return v___x_1692_;
}
else
{
lean_object* v_toCold_1693_; lean_object* v_options_1694_; lean_object* v_inheritedTraceOptions_1695_; uint8_t v_hasTrace_1696_; lean_object* v___x_1697_; lean_object* v_a_1698_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; 
v_toCold_1693_ = lean_ctor_get(v___y_1688_, 0);
v_options_1694_ = lean_ctor_get(v_toCold_1693_, 2);
v_inheritedTraceOptions_1695_ = lean_ctor_get(v_toCold_1693_, 11);
v_hasTrace_1696_ = lean_ctor_get_uint8(v_options_1694_, sizeof(void*)*1);
v___x_1697_ = lean_box(0);
v_a_1698_ = lean_array_uget_borrowed(v_as_1676_, v_i_1678_);
if (v_hasTrace_1696_ == 0)
{
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1725_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1726_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1695_, v_options_1694_, v___x_1726_);
if (v___x_1727_ == 0)
{
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Meta_Grind_updateLastTag(v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref_known(v___x_1728_, 1);
v___x_1729_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1698_, v___y_1680_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1698_);
v___x_1732_ = l_Lean_MessageData_ofExpr(v_a_1698_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1730_);
lean_dec(v_a_1730_);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1736_, v___x_1737_);
v___x_1739_ = l_Lean_MessageData_ofList(v___x_1738_);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1735_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1725_, v___x_1740_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec_ref_known(v___x_1741_, 1);
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
goto v___jp_1699_;
}
else
{
return v___x_1741_;
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
v_a_1742_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1729_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1729_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
return v___x_1728_;
}
}
}
v___jp_1699_:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1698_, v___y_1700_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1711_);
lean_dec(v_a_1711_);
v___x_1713_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1674_, v_lams_1675_, v___x_1712_, v___x_1712_, v___x_1697_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 0)
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1678_, v___x_1714_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1674_, v_lams_1675_, v_as_1676_, v_sz_1677_, v___x_1715_, v___x_1697_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1716_;
}
else
{
return v___x_1713_;
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1710_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1710_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1750_ = _args[0];
lean_object* v_lams_1751_ = _args[1];
lean_object* v_as_1752_ = _args[2];
lean_object* v_sz_1753_ = _args[3];
lean_object* v_i_1754_ = _args[4];
lean_object* v_b_1755_ = _args[5];
lean_object* v___y_1756_ = _args[6];
lean_object* v___y_1757_ = _args[7];
lean_object* v___y_1758_ = _args[8];
lean_object* v___y_1759_ = _args[9];
lean_object* v___y_1760_ = _args[10];
lean_object* v___y_1761_ = _args[11];
lean_object* v___y_1762_ = _args[12];
lean_object* v___y_1763_ = _args[13];
lean_object* v___y_1764_ = _args[14];
lean_object* v___y_1765_ = _args[15];
lean_object* v___y_1766_ = _args[16];
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1750_, v_lams_1751_, v_as_1752_, v_sz_boxed_1767_, v_i_boxed_1768_, v_b_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v_as_1752_);
lean_dec_ref(v_lams_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1769_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1776_, lean_object* v_fns_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_array_get_size(v_lams_1776_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1792_ = l_Lean_instInhabitedExpr;
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_nat_sub(v___x_1789_, v___x_1793_);
v___x_1795_ = lean_array_get_borrowed(v___x_1792_, v_lams_1776_, v___x_1794_);
lean_dec(v___x_1794_);
v___x_1796_ = lean_st_ref_get(v_a_1778_);
lean_inc(v___x_1795_);
v___x_1797_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1796_, v___x_1795_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v___x_1796_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v_toCold_1822_; lean_object* v_options_1823_; uint8_t v_hasTrace_1824_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v_toCold_1822_ = lean_ctor_get(v_a_1786_, 0);
v_options_1823_ = lean_ctor_get(v_toCold_1822_, 2);
v_hasTrace_1824_ = lean_ctor_get_uint8(v_options_1823_, sizeof(void*)*1);
if (v_hasTrace_1824_ == 0)
{
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
goto v___jp_1799_;
}
else
{
lean_object* v_inheritedTraceOptions_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_inheritedTraceOptions_1825_ = lean_ctor_get(v_toCold_1822_, 11);
v___x_1826_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1827_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1828_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1825_, v_options_1823_, v___x_1827_);
if (v___x_1828_ == 0)
{
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Meta_Grind_updateLastTag(v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_dec_ref_known(v___x_1829_, 1);
v___x_1830_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1777_);
v___x_1831_ = lean_array_to_list(v_fns_1777_);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1831_, v___x_1832_);
v___x_1834_ = l_Lean_MessageData_ofList(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1830_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
lean_inc_ref(v_lams_1776_);
v___x_1838_ = lean_array_to_list(v_lams_1776_);
v___x_1839_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1838_, v___x_1832_);
v___x_1840_ = l_Lean_MessageData_ofList(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1837_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1826_, v___x_1841_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_dec_ref_known(v___x_1842_, 1);
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
goto v___jp_1799_;
}
else
{
lean_dec(v_a_1798_);
lean_dec_ref(v_fns_1777_);
lean_dec_ref(v_lams_1776_);
return v___x_1842_;
}
}
else
{
lean_dec(v_a_1798_);
lean_dec_ref(v_fns_1777_);
lean_dec_ref(v_lams_1776_);
return v___x_1829_;
}
}
}
v___jp_1799_:
{
lean_object* v___x_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_box(0);
v_sz_1811_ = lean_array_size(v_fns_1777_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1798_, v_lams_1776_, v_fns_1777_, v_sz_1811_, v___x_1812_, v___x_1810_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec_ref(v_fns_1777_);
lean_dec_ref(v_lams_1776_);
lean_dec(v_a_1798_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1813_, 0);
lean_dec(v_unused_1821_);
v___x_1815_ = v___x_1813_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v___x_1813_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1810_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1810_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v_fns_1777_);
lean_dec_ref(v_lams_1776_);
v_a_1843_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1797_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1797_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v_fns_1777_);
lean_dec_ref(v_lams_1776_);
v___x_1851_ = lean_box(0);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1853_, lean_object* v_fns_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1853_, v_fns_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec(v_a_1855_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_lams_1869_, lean_object* v_inst_1870_, lean_object* v_a_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1867_, v_a_1868_, v_lams_1869_, v_a_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_lams_1886_, lean_object* v_inst_1887_, lean_object* v_a_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1884_, v_a_1885_, v_lams_1886_, v_inst_1887_, v_a_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v_lams_1886_);
lean_dec_ref(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1901_, lean_object* v_lams_1902_, lean_object* v_as_1903_, lean_object* v_as_x27_1904_, lean_object* v_b_1905_, lean_object* v_a_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1901_, v_lams_1902_, v_as_1903_, v_as_x27_1904_, v_b_1905_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1919_ = _args[0];
lean_object* v_lams_1920_ = _args[1];
lean_object* v_as_1921_ = _args[2];
lean_object* v_as_x27_1922_ = _args[3];
lean_object* v_b_1923_ = _args[4];
lean_object* v_a_1924_ = _args[5];
lean_object* v___y_1925_ = _args[6];
lean_object* v___y_1926_ = _args[7];
lean_object* v___y_1927_ = _args[8];
lean_object* v___y_1928_ = _args[9];
lean_object* v___y_1929_ = _args[10];
lean_object* v___y_1930_ = _args[11];
lean_object* v___y_1931_ = _args[12];
lean_object* v___y_1932_ = _args[13];
lean_object* v___y_1933_ = _args[14];
lean_object* v___y_1934_ = _args[15];
lean_object* v___y_1935_ = _args[16];
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1919_, v_lams_1920_, v_as_1921_, v_as_x27_1922_, v_b_1923_, v_a_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v_as_x27_1922_);
lean_dec(v_as_1921_);
lean_dec_ref(v_lams_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1937_, lean_object* v_lams_1938_, lean_object* v_as_1939_, lean_object* v_as_x27_1940_, lean_object* v_b_1941_, lean_object* v_a_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1937_, v_lams_1938_, v_as_x27_1940_, v_b_1941_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1955_ = _args[0];
lean_object* v_lams_1956_ = _args[1];
lean_object* v_as_1957_ = _args[2];
lean_object* v_as_x27_1958_ = _args[3];
lean_object* v_b_1959_ = _args[4];
lean_object* v_a_1960_ = _args[5];
lean_object* v___y_1961_ = _args[6];
lean_object* v___y_1962_ = _args[7];
lean_object* v___y_1963_ = _args[8];
lean_object* v___y_1964_ = _args[9];
lean_object* v___y_1965_ = _args[10];
lean_object* v___y_1966_ = _args[11];
lean_object* v___y_1967_ = _args[12];
lean_object* v___y_1968_ = _args[13];
lean_object* v___y_1969_ = _args[14];
lean_object* v___y_1970_ = _args[15];
lean_object* v___y_1971_ = _args[16];
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1955_, v_lams_1956_, v_as_1957_, v_as_x27_1958_, v_b_1959_, v_a_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v_as_x27_1958_);
lean_dec(v_as_1957_);
lean_dec_ref(v_lams_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1976_, lean_object* v_as_1977_, size_t v_sz_1978_, size_t v_i_1979_, lean_object* v_b_1980_){
_start:
{
lean_object* v_a_1982_; uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_lt(v_i_1979_, v_sz_1978_);
if (v___x_1986_ == 0)
{
lean_inc_ref(v_b_1980_);
return v_b_1980_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_a_1989_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1989_ = lean_array_uget_borrowed(v_as_1977_, v_i_1979_);
if (lean_obj_tag(v_a_1989_) == 6)
{
lean_object* v_binderType_1990_; size_t v___x_1991_; size_t v___x_1992_; uint8_t v___x_1993_; 
v_binderType_1990_ = lean_ctor_get(v_a_1989_, 1);
v___x_1991_ = lean_ptr_addr(v_d_1976_);
v___x_1992_ = lean_ptr_addr(v_binderType_1990_);
v___x_1993_ = lean_usize_dec_eq(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
v_a_1982_ = v___x_1988_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v_a_1989_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_a_1989_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v___x_1987_);
return v___x_1996_;
}
}
else
{
v_a_1982_ = v___x_1988_;
goto v___jp_1981_;
}
}
v___jp_1981_:
{
size_t v___x_1983_; size_t v___x_1984_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1979_, v___x_1983_);
v_i_1979_ = v___x_1984_;
v_b_1980_ = v_a_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1997_, lean_object* v_as_1998_, lean_object* v_sz_1999_, lean_object* v_i_2000_, lean_object* v_b_2001_){
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1999_);
lean_dec(v_sz_1999_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_2000_);
lean_dec(v_i_2000_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1997_, v_as_1998_, v_sz_boxed_2002_, v_i_boxed_2003_, v_b_2001_);
lean_dec_ref(v_b_2001_);
lean_dec_ref(v_as_1998_);
lean_dec_ref(v_d_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2005_, lean_object* v_d_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; size_t v_sz_2009_; size_t v___x_2010_; lean_object* v___x_2011_; lean_object* v_fst_2012_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2009_ = lean_array_size(v_lams_2005_);
v___x_2010_ = ((size_t)0ULL);
v___x_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2006_, v_lams_2005_, v_sz_2009_, v___x_2010_, v___x_2008_);
v_fst_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_fst_2012_);
lean_dec_ref(v___x_2011_);
if (lean_obj_tag(v_fst_2012_) == 0)
{
return v___x_2007_;
}
else
{
lean_object* v_val_2013_; 
v_val_2013_ = lean_ctor_get(v_fst_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_fst_2012_, 1);
return v_val_2013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2014_, lean_object* v_d_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2014_, v_d_2015_);
lean_dec_ref(v_d_2015_);
lean_dec_ref(v_lams_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2027_, lean_object* v_lams_u2081_2028_, lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_a_2045_; uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2031_, v_sz_2030_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2032_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v_a_2052_; 
v___x_2051_ = lean_box(0);
v_a_2052_ = lean_array_uget_borrowed(v_as_2029_, v_i_2031_);
if (lean_obj_tag(v_a_2052_) == 6)
{
lean_object* v_binderType_2053_; lean_object* v_body_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_binderType_2053_ = lean_ctor_get(v_a_2052_, 1);
v_body_2054_ = lean_ctor_get(v_a_2052_, 2);
v___x_2055_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2053_);
v___x_2056_ = l_Lean_Meta_getLevel(v_binderType_2053_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_a_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
lean_inc_ref(v___x_2060_);
v___x_2061_ = l_Lean_mkConst(v___x_2058_, v___x_2060_);
lean_inc_ref(v_binderType_2053_);
v___x_2062_ = l_Lean_Expr_app___override(v___x_2061_, v_binderType_2053_);
v___x_2063_ = lean_box(0);
v___x_2064_ = l_Lean_Meta_synthInstance_x3f(v___x_2062_, v___x_2063_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; uint8_t v___x_2131_; 
v_val_2066_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v_a_2065_, 1);
v___x_2131_ = l_Lean_Expr_hasLooseBVars(v_body_2054_);
if (v___x_2131_ == 0)
{
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2060_);
v___x_2133_ = l_Lean_mkConst(v___x_2132_, v___x_2060_);
lean_inc_ref(v_binderType_2053_);
v___x_2134_ = l_Lean_Expr_app___override(v___x_2133_, v_binderType_2053_);
v___x_2135_ = l_Lean_Meta_synthInstance_x3f(v___x_2134_, v___x_2063_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
if (lean_obj_tag(v_a_2136_) == 0)
{
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
else
{
lean_dec_ref_known(v_a_2136_, 1);
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
goto v___jp_2067_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
v___jp_2067_:
{
lean_object* v___x_2078_; 
v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2027_, v_binderType_2053_);
if (lean_obj_tag(v___x_2078_) == 1)
{
lean_object* v_val_2079_; 
v_val_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2078_, 1);
if (lean_obj_tag(v_val_2079_) == 6)
{
lean_object* v_binderType_2080_; lean_object* v_body_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_binderType_2080_ = lean_ctor_get(v_val_2079_, 1);
lean_inc_ref(v_binderType_2080_);
v_body_2081_ = lean_ctor_get(v_val_2079_, 2);
lean_inc_ref(v_body_2081_);
lean_dec_ref_known(v_val_2079_, 3);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2083_ = l_Lean_mkConst(v___x_2082_, v___x_2060_);
v___x_2084_ = l_Lean_mkAppB(v___x_2083_, v_binderType_2080_, v_val_2066_);
v___x_2085_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2084_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_expr_instantiate1(v_body_2054_, v_a_2086_);
v___x_2088_ = lean_expr_instantiate1(v_body_2081_, v_a_2086_);
lean_dec_ref(v_body_2081_);
v___x_2089_ = lean_array_fget_borrowed(v_lams_u2081_2028_, v___x_2055_);
v___x_2090_ = lean_array_fget_borrowed(v_lams_u2082_2027_, v___x_2055_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc(v___x_2090_);
lean_inc(v___x_2089_);
v___x_2091_ = lean_grind_mk_eq_proof(v___x_2089_, v___x_2090_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_mkCongrFun(v_a_2092_, v_a_2086_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_Meta_mkEq(v___x_2087_, v___x_2088_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l_Lean_Meta_mkExpectedPropHint(v_a_2094_, v_a_2096_);
v___x_2098_ = l_Lean_Meta_Grind_pushNewFact(v___x_2097_, v___x_2055_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
else
{
return v___x_2098_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2094_);
v_a_2099_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2095_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2095_);
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
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
v_a_2107_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2093_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2093_);
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
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_a_2086_);
v_a_2115_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2091_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2091_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v_body_2081_);
v_a_2123_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2085_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2085_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_dec(v_val_2079_);
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
else
{
lean_dec(v___x_2078_);
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
}
else
{
lean_dec(v_a_2065_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref_known(v___x_2060_, 2);
v_a_2145_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2064_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2064_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
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
v_a_2153_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2056_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2056_);
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
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
v___jp_2044_:
{
size_t v___x_2046_; size_t v___x_2047_; 
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_i_2031_, v___x_2046_);
v_i_2031_ = v___x_2047_;
v_b_2032_ = v_a_2045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2161_ = _args[0];
lean_object* v_lams_u2081_2162_ = _args[1];
lean_object* v_as_2163_ = _args[2];
lean_object* v_sz_2164_ = _args[3];
lean_object* v_i_2165_ = _args[4];
lean_object* v_b_2166_ = _args[5];
lean_object* v___y_2167_ = _args[6];
lean_object* v___y_2168_ = _args[7];
lean_object* v___y_2169_ = _args[8];
lean_object* v___y_2170_ = _args[9];
lean_object* v___y_2171_ = _args[10];
lean_object* v___y_2172_ = _args[11];
lean_object* v___y_2173_ = _args[12];
lean_object* v___y_2174_ = _args[13];
lean_object* v___y_2175_ = _args[14];
lean_object* v___y_2176_ = _args[15];
lean_object* v___y_2177_ = _args[16];
_start:
{
size_t v_sz_boxed_2178_; size_t v_i_boxed_2179_; lean_object* v_res_2180_; 
v_sz_boxed_2178_ = lean_unbox_usize(v_sz_2164_);
lean_dec(v_sz_2164_);
v_i_boxed_2179_ = lean_unbox_usize(v_i_2165_);
lean_dec(v_i_2165_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2161_, v_lams_u2081_2162_, v_as_2163_, v_sz_boxed_2178_, v_i_boxed_2179_, v_b_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v_as_2163_);
lean_dec_ref(v_lams_u2081_2162_);
lean_dec_ref(v_lams_u2082_2161_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2181_, lean_object* v_lams_u2082_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2194_ = lean_array_get_size(v_lams_u2081_2181_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_nat_dec_eq(v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = lean_array_get_size(v_lams_u2082_2182_);
v___x_2198_ = lean_nat_dec_eq(v___x_2197_, v___x_2195_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = lean_box(0);
v_sz_2200_ = lean_array_size(v_lams_u2081_2181_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2182_, v_lams_u2081_2181_, v_lams_u2081_2181_, v_sz_2200_, v___x_2201_, v___x_2199_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2210_);
v___x_2204_ = v___x_2202_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2199_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2199_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
return v___x_2202_;
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2215_, lean_object* v_lams_u2082_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2215_, v_lams_u2082_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
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
lean_dec_ref(v_lams_u2082_2216_);
lean_dec_ref(v_lams_u2081_2215_);
return v_res_2228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2231_){
_start:
{
uint8_t v_res_2232_; lean_object* v_r_2233_; 
v_res_2232_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2231_);
lean_dec_ref(v_x_2231_);
v_r_2233_ = lean_box(v_res_2232_);
return v_r_2233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_){
_start:
{
uint8_t v___x_2236_; 
v___x_2236_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2237_, lean_object* v_x_2238_){
_start:
{
uint8_t v_res_2239_; lean_object* v_r_2240_; 
v_res_2239_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2237_, v_x_2238_);
lean_dec_ref(v_x_2238_);
v_r_2240_ = lean_box(v_res_2239_);
return v_r_2240_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2241_, lean_object* v_v_2242_, lean_object* v_i_2243_){
_start:
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_array_get_size(v_xs_2241_);
v___x_2245_ = lean_nat_dec_lt(v_i_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec(v_i_2243_);
v___x_2246_ = lean_box(0);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; uint8_t v___x_2250_; 
v___x_2247_ = lean_array_fget_borrowed(v_xs_2241_, v_i_2243_);
v___x_2248_ = lean_ptr_addr(v___x_2247_);
v___x_2249_ = lean_ptr_addr(v_v_2242_);
v___x_2250_ = lean_usize_dec_eq(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_add(v_i_2243_, v___x_2251_);
lean_dec(v_i_2243_);
v_i_2243_ = v___x_2252_;
goto _start;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_i_2243_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2255_, lean_object* v_v_2256_, lean_object* v_i_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2255_, v_v_2256_, v_i_2257_);
lean_dec_ref(v_v_2256_);
lean_dec_ref(v_xs_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2259_, lean_object* v_v_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2259_, v_v_2260_, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2263_, lean_object* v_v_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2263_, v_v_2264_);
lean_dec_ref(v_v_2264_);
lean_dec_ref(v_xs_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2266_, size_t v_x_2267_, lean_object* v_x_2268_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_es_2269_; lean_object* v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; lean_object* v_j_2273_; lean_object* v_entry_2274_; 
v_es_2269_ = lean_ctor_get(v_x_2266_, 0);
v___x_2270_ = lean_box(2);
v___x_2271_ = ((size_t)31ULL);
v___x_2272_ = lean_usize_land(v_x_2267_, v___x_2271_);
v_j_2273_ = lean_usize_to_nat(v___x_2272_);
v_entry_2274_ = lean_array_get(v___x_2270_, v_es_2269_, v_j_2273_);
switch(lean_obj_tag(v_entry_2274_))
{
case 0:
{
lean_object* v_key_2275_; size_t v___x_2276_; size_t v___x_2277_; uint8_t v___x_2278_; 
v_key_2275_ = lean_ctor_get(v_entry_2274_, 0);
lean_inc(v_key_2275_);
lean_dec_ref_known(v_entry_2274_, 2);
v___x_2276_ = lean_ptr_addr(v_x_2268_);
v___x_2277_ = lean_ptr_addr(v_key_2275_);
lean_dec(v_key_2275_);
v___x_2278_ = lean_usize_dec_eq(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec(v_j_2273_);
return v_x_2266_;
}
else
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2286_; 
lean_inc_ref(v_es_2269_);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_x_2266_, 0);
lean_dec(v_unused_2287_);
v___x_2280_ = v_x_2266_;
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v_x_2266_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_array_set(v_es_2269_, v_j_2273_, v___x_2270_);
lean_dec(v_j_2273_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
case 1:
{
lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2322_; 
lean_inc_ref(v_es_2269_);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_x_2266_, 0);
lean_dec(v_unused_2323_);
v___x_2289_ = v_x_2266_;
v_isShared_2290_ = v_isSharedCheck_2322_;
goto v_resetjp_2288_;
}
else
{
lean_dec(v_x_2266_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2322_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_node_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2321_; 
v_node_2291_ = lean_ctor_get(v_entry_2274_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_entry_2274_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2293_ = v_entry_2274_;
v_isShared_2294_ = v_isSharedCheck_2321_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_node_2291_);
lean_dec(v_entry_2274_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2321_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
size_t v___x_2295_; lean_object* v_entries_2296_; size_t v___x_2297_; lean_object* v_newNode_2298_; lean_object* v___x_2299_; 
v___x_2295_ = ((size_t)5ULL);
v_entries_2296_ = lean_array_set(v_es_2269_, v_j_2273_, v___x_2270_);
v___x_2297_ = lean_usize_shift_right(v_x_2267_, v___x_2295_);
v_newNode_2298_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2291_, v___x_2297_, v_x_2268_);
lean_inc_ref(v_newNode_2298_);
v___x_2299_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2301_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v_newNode_2298_);
v___x_2301_ = v___x_2293_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_newNode_2298_);
v___x_2301_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_array_set(v_entries_2296_, v_j_2273_, v___x_2301_);
lean_dec(v_j_2273_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2302_);
v___x_2304_ = v___x_2289_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_val_2307_; lean_object* v_fst_2308_; lean_object* v_snd_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v_newNode_2298_);
lean_del_object(v___x_2293_);
v_val_2307_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_2299_, 1);
v_fst_2308_ = lean_ctor_get(v_val_2307_, 0);
v_snd_2309_ = lean_ctor_get(v_val_2307_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_val_2307_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2311_ = v_val_2307_;
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snd_2309_);
lean_inc(v_fst_2308_);
lean_dec(v_val_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_snd_2309_);
v___x_2314_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2315_ = lean_array_set(v_entries_2296_, v_j_2273_, v___x_2314_);
lean_dec(v_j_2273_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2315_);
v___x_2317_ = v___x_2289_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
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
}
}
default: 
{
lean_dec(v_j_2273_);
return v_x_2266_;
}
}
}
else
{
lean_object* v_ks_2324_; lean_object* v_vs_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2339_; 
v_ks_2324_ = lean_ctor_get(v_x_2266_, 0);
v_vs_2325_ = lean_ctor_get(v_x_2266_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2327_ = v_x_2266_;
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_vs_2325_);
lean_inc(v_ks_2324_);
lean_dec(v_x_2266_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2339_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2324_, v_x_2268_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2331_; 
if (v_isShared_2328_ == 0)
{
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_ks_2324_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_vs_2325_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
else
{
lean_object* v_val_2333_; lean_object* v_keys_x27_2334_; lean_object* v_vals_x27_2335_; lean_object* v___x_2337_; 
v_val_2333_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_n(v_val_2333_, 2);
lean_dec_ref_known(v___x_2329_, 1);
v_keys_x27_2334_ = l_Array_eraseIdx___redArg(v_ks_2324_, v_val_2333_);
v_vals_x27_2335_ = l_Array_eraseIdx___redArg(v_vs_2325_, v_val_2333_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v_vals_x27_2335_);
lean_ctor_set(v___x_2327_, 0, v_keys_x27_2334_);
v___x_2337_ = v___x_2327_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_keys_x27_2334_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_vals_x27_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
size_t v_x_19465__boxed_2343_; lean_object* v_res_2344_; 
v_x_19465__boxed_2343_ = lean_unbox_usize(v_x_2341_);
lean_dec(v_x_2341_);
v_res_2344_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2340_, v_x_19465__boxed_2343_, v_x_2342_);
lean_dec_ref(v_x_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v___x_2347_; size_t v___x_2348_; size_t v___x_2349_; uint64_t v___x_2350_; size_t v_h_2351_; lean_object* v___x_2352_; 
v___x_2347_ = lean_ptr_addr(v_x_2346_);
v___x_2348_ = ((size_t)3ULL);
v___x_2349_ = lean_usize_shift_right(v___x_2347_, v___x_2348_);
v___x_2350_ = lean_usize_to_uint64(v___x_2349_);
v_h_2351_ = lean_uint64_to_usize(v___x_2350_);
v___x_2352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2345_, v_h_2351_, v_x_2346_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2353_, v_x_2354_);
lean_dec_ref(v_x_2354_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
if (lean_obj_tag(v_as_2356_) == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
else
{
lean_object* v_head_2370_; lean_object* v_tail_2371_; lean_object* v___x_2372_; 
v_head_2370_ = lean_ctor_get(v_as_2356_, 0);
lean_inc(v_head_2370_);
v_tail_2371_ = lean_ctor_get(v_as_2356_, 1);
lean_inc(v_tail_2371_);
lean_dec_ref_known(v_as_2356_, 2);
v___x_2372_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2370_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref_known(v___x_2372_, 1);
v_as_2356_ = v_tail_2371_;
goto _start;
}
else
{
lean_dec(v_tail_2371_);
return v___x_2372_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2387_, lean_object* v_vals_2388_, lean_object* v_i_2389_, lean_object* v_k_2390_){
_start:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = lean_array_get_size(v_keys_2387_);
v___x_2392_ = lean_nat_dec_lt(v_i_2389_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v_i_2389_);
v___x_2393_ = lean_box(0);
return v___x_2393_;
}
else
{
lean_object* v_k_x27_2394_; size_t v___x_2395_; size_t v___x_2396_; uint8_t v___x_2397_; 
v_k_x27_2394_ = lean_array_fget_borrowed(v_keys_2387_, v_i_2389_);
v___x_2395_ = lean_ptr_addr(v_k_2390_);
v___x_2396_ = lean_ptr_addr(v_k_x27_2394_);
v___x_2397_ = lean_usize_dec_eq(v___x_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v_i_2389_, v___x_2398_);
lean_dec(v_i_2389_);
v_i_2389_ = v___x_2399_;
goto _start;
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_array_fget_borrowed(v_vals_2388_, v_i_2389_);
lean_dec(v_i_2389_);
lean_inc(v___x_2401_);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2403_, lean_object* v_vals_2404_, lean_object* v_i_2405_, lean_object* v_k_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2403_, v_vals_2404_, v_i_2405_, v_k_2406_);
lean_dec_ref(v_k_2406_);
lean_dec_ref(v_vals_2404_);
lean_dec_ref(v_keys_2403_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2408_, size_t v_x_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v_es_2411_; lean_object* v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; lean_object* v_j_2415_; lean_object* v___x_2416_; 
v_es_2411_ = lean_ctor_get(v_x_2408_, 0);
v___x_2412_ = lean_box(2);
v___x_2413_ = ((size_t)31ULL);
v___x_2414_ = lean_usize_land(v_x_2409_, v___x_2413_);
v_j_2415_ = lean_usize_to_nat(v___x_2414_);
v___x_2416_ = lean_array_get_borrowed(v___x_2412_, v_es_2411_, v_j_2415_);
lean_dec(v_j_2415_);
switch(lean_obj_tag(v___x_2416_))
{
case 0:
{
lean_object* v_key_2417_; lean_object* v_val_2418_; size_t v___x_2419_; size_t v___x_2420_; uint8_t v___x_2421_; 
v_key_2417_ = lean_ctor_get(v___x_2416_, 0);
v_val_2418_ = lean_ctor_get(v___x_2416_, 1);
v___x_2419_ = lean_ptr_addr(v_x_2410_);
v___x_2420_ = lean_ptr_addr(v_key_2417_);
v___x_2421_ = lean_usize_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_box(0);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
lean_inc(v_val_2418_);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_val_2418_);
return v___x_2423_;
}
}
case 1:
{
lean_object* v_node_2424_; size_t v___x_2425_; size_t v___x_2426_; 
v_node_2424_ = lean_ctor_get(v___x_2416_, 0);
v___x_2425_ = ((size_t)5ULL);
v___x_2426_ = lean_usize_shift_right(v_x_2409_, v___x_2425_);
v_x_2408_ = v_node_2424_;
v_x_2409_ = v___x_2426_;
goto _start;
}
default: 
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_box(0);
return v___x_2428_;
}
}
}
else
{
lean_object* v_ks_2429_; lean_object* v_vs_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_ks_2429_ = lean_ctor_get(v_x_2408_, 0);
v_vs_2430_ = lean_ctor_get(v_x_2408_, 1);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2429_, v_vs_2430_, v___x_2431_, v_x_2410_);
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
size_t v_x_19690__boxed_2436_; lean_object* v_res_2437_; 
v_x_19690__boxed_2436_ = lean_unbox_usize(v_x_2434_);
lean_dec(v_x_2434_);
v_res_2437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2433_, v_x_19690__boxed_2436_, v_x_2435_);
lean_dec_ref(v_x_2435_);
lean_dec_ref(v_x_2433_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
size_t v___x_2440_; size_t v___x_2441_; size_t v___x_2442_; uint64_t v___x_2443_; size_t v___x_2444_; lean_object* v___x_2445_; 
v___x_2440_ = lean_ptr_addr(v_x_2439_);
v___x_2441_ = ((size_t)3ULL);
v___x_2442_ = lean_usize_shift_right(v___x_2440_, v___x_2441_);
v___x_2443_ = lean_usize_to_uint64(v___x_2442_);
v___x_2444_ = lean_uint64_to_usize(v___x_2443_);
v___x_2445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2438_, v___x_2444_, v_x_2439_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2446_, v_x_2447_);
lean_dec_ref(v_x_2447_);
lean_dec_ref(v_x_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
if (lean_obj_tag(v_as_x27_2449_) == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_b_2450_);
return v___x_2462_;
}
else
{
lean_object* v_head_2463_; lean_object* v_tail_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_toGoalState_2467_; lean_object* v_ematch_2468_; lean_object* v_delayedThmInsts_2469_; lean_object* v___x_2470_; 
v_head_2463_ = lean_ctor_get(v_as_x27_2449_, 0);
v_tail_2464_ = lean_ctor_get(v_as_x27_2449_, 1);
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_st_ref_get(v___y_2451_);
v_toGoalState_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_toGoalState_2467_);
lean_dec(v___x_2466_);
v_ematch_2468_ = lean_ctor_get(v_toGoalState_2467_, 13);
lean_inc_ref(v_ematch_2468_);
lean_dec_ref(v_toGoalState_2467_);
v_delayedThmInsts_2469_ = lean_ctor_get(v_ematch_2468_, 10);
lean_inc_ref(v_delayedThmInsts_2469_);
lean_dec_ref(v_ematch_2468_);
v___x_2470_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2469_, v_head_2463_);
lean_dec_ref(v_delayedThmInsts_2469_);
if (lean_obj_tag(v___x_2470_) == 1)
{
lean_object* v_val_2471_; lean_object* v___x_2472_; lean_object* v_toGoalState_2473_; lean_object* v_ematch_2474_; lean_object* v_mvarId_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2530_; 
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = lean_st_ref_take(v___y_2451_);
v_toGoalState_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_toGoalState_2473_);
v_ematch_2474_ = lean_ctor_get(v_toGoalState_2473_, 13);
lean_inc_ref(v_ematch_2474_);
v_mvarId_2475_ = lean_ctor_get(v___x_2472_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2472_, 0);
lean_dec(v_unused_2531_);
v___x_2477_ = v___x_2472_;
v_isShared_2478_ = v_isSharedCheck_2530_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_mvarId_2475_);
lean_dec(v___x_2472_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2530_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_nextDeclIdx_2479_; lean_object* v_enodeMap_2480_; lean_object* v_exprs_2481_; lean_object* v_parents_2482_; lean_object* v_congrTable_2483_; lean_object* v_appMap_2484_; lean_object* v_indicesFound_2485_; lean_object* v_toProcess_2486_; lean_object* v_internalizing_2487_; uint8_t v_inconsistent_2488_; lean_object* v_nextIdx_2489_; lean_object* v_newRawFacts_2490_; lean_object* v_facts_2491_; lean_object* v_extThms_2492_; lean_object* v_inj_2493_; lean_object* v_split_2494_; lean_object* v_clean_2495_; lean_object* v_sstates_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2528_; 
v_nextDeclIdx_2479_ = lean_ctor_get(v_toGoalState_2473_, 0);
v_enodeMap_2480_ = lean_ctor_get(v_toGoalState_2473_, 1);
v_exprs_2481_ = lean_ctor_get(v_toGoalState_2473_, 2);
v_parents_2482_ = lean_ctor_get(v_toGoalState_2473_, 3);
v_congrTable_2483_ = lean_ctor_get(v_toGoalState_2473_, 4);
v_appMap_2484_ = lean_ctor_get(v_toGoalState_2473_, 5);
v_indicesFound_2485_ = lean_ctor_get(v_toGoalState_2473_, 6);
v_toProcess_2486_ = lean_ctor_get(v_toGoalState_2473_, 7);
v_internalizing_2487_ = lean_ctor_get(v_toGoalState_2473_, 8);
v_inconsistent_2488_ = lean_ctor_get_uint8(v_toGoalState_2473_, sizeof(void*)*18);
v_nextIdx_2489_ = lean_ctor_get(v_toGoalState_2473_, 9);
v_newRawFacts_2490_ = lean_ctor_get(v_toGoalState_2473_, 10);
v_facts_2491_ = lean_ctor_get(v_toGoalState_2473_, 11);
v_extThms_2492_ = lean_ctor_get(v_toGoalState_2473_, 12);
v_inj_2493_ = lean_ctor_get(v_toGoalState_2473_, 14);
v_split_2494_ = lean_ctor_get(v_toGoalState_2473_, 15);
v_clean_2495_ = lean_ctor_get(v_toGoalState_2473_, 16);
v_sstates_2496_ = lean_ctor_get(v_toGoalState_2473_, 17);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_toGoalState_2473_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_toGoalState_2473_, 13);
lean_dec(v_unused_2529_);
v___x_2498_ = v_toGoalState_2473_;
v_isShared_2499_ = v_isSharedCheck_2528_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_sstates_2496_);
lean_inc(v_clean_2495_);
lean_inc(v_split_2494_);
lean_inc(v_inj_2493_);
lean_inc(v_extThms_2492_);
lean_inc(v_facts_2491_);
lean_inc(v_newRawFacts_2490_);
lean_inc(v_nextIdx_2489_);
lean_inc(v_internalizing_2487_);
lean_inc(v_toProcess_2486_);
lean_inc(v_indicesFound_2485_);
lean_inc(v_appMap_2484_);
lean_inc(v_congrTable_2483_);
lean_inc(v_parents_2482_);
lean_inc(v_exprs_2481_);
lean_inc(v_enodeMap_2480_);
lean_inc(v_nextDeclIdx_2479_);
lean_dec(v_toGoalState_2473_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2528_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_thmMap_2500_; lean_object* v_gmt_2501_; lean_object* v_thms_2502_; lean_object* v_newThms_2503_; lean_object* v_numInstances_2504_; lean_object* v_numDelayedInstances_2505_; lean_object* v_num_2506_; lean_object* v_preInstances_2507_; lean_object* v_nextThmIdx_2508_; lean_object* v_matchEqNames_2509_; lean_object* v_delayedThmInsts_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2527_; 
v_thmMap_2500_ = lean_ctor_get(v_ematch_2474_, 0);
v_gmt_2501_ = lean_ctor_get(v_ematch_2474_, 1);
v_thms_2502_ = lean_ctor_get(v_ematch_2474_, 2);
v_newThms_2503_ = lean_ctor_get(v_ematch_2474_, 3);
v_numInstances_2504_ = lean_ctor_get(v_ematch_2474_, 4);
v_numDelayedInstances_2505_ = lean_ctor_get(v_ematch_2474_, 5);
v_num_2506_ = lean_ctor_get(v_ematch_2474_, 6);
v_preInstances_2507_ = lean_ctor_get(v_ematch_2474_, 7);
v_nextThmIdx_2508_ = lean_ctor_get(v_ematch_2474_, 8);
v_matchEqNames_2509_ = lean_ctor_get(v_ematch_2474_, 9);
v_delayedThmInsts_2510_ = lean_ctor_get(v_ematch_2474_, 10);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_ematch_2474_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2512_ = v_ematch_2474_;
v_isShared_2513_ = v_isSharedCheck_2527_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_delayedThmInsts_2510_);
lean_inc(v_matchEqNames_2509_);
lean_inc(v_nextThmIdx_2508_);
lean_inc(v_preInstances_2507_);
lean_inc(v_num_2506_);
lean_inc(v_numDelayedInstances_2505_);
lean_inc(v_numInstances_2504_);
lean_inc(v_newThms_2503_);
lean_inc(v_thms_2502_);
lean_inc(v_gmt_2501_);
lean_inc(v_thmMap_2500_);
lean_dec(v_ematch_2474_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2527_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2514_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2510_, v_head_2463_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 10, v___x_2514_);
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_thmMap_2500_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_gmt_2501_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_thms_2502_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_newThms_2503_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v_numInstances_2504_);
lean_ctor_set(v_reuseFailAlloc_2526_, 5, v_numDelayedInstances_2505_);
lean_ctor_set(v_reuseFailAlloc_2526_, 6, v_num_2506_);
lean_ctor_set(v_reuseFailAlloc_2526_, 7, v_preInstances_2507_);
lean_ctor_set(v_reuseFailAlloc_2526_, 8, v_nextThmIdx_2508_);
lean_ctor_set(v_reuseFailAlloc_2526_, 9, v_matchEqNames_2509_);
lean_ctor_set(v_reuseFailAlloc_2526_, 10, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 13, v___x_2516_);
v___x_2518_ = v___x_2498_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_nextDeclIdx_2479_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_enodeMap_2480_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_exprs_2481_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_parents_2482_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_congrTable_2483_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v_appMap_2484_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_indicesFound_2485_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_toProcess_2486_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_internalizing_2487_);
lean_ctor_set(v_reuseFailAlloc_2525_, 9, v_nextIdx_2489_);
lean_ctor_set(v_reuseFailAlloc_2525_, 10, v_newRawFacts_2490_);
lean_ctor_set(v_reuseFailAlloc_2525_, 11, v_facts_2491_);
lean_ctor_set(v_reuseFailAlloc_2525_, 12, v_extThms_2492_);
lean_ctor_set(v_reuseFailAlloc_2525_, 13, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2525_, 14, v_inj_2493_);
lean_ctor_set(v_reuseFailAlloc_2525_, 15, v_split_2494_);
lean_ctor_set(v_reuseFailAlloc_2525_, 16, v_clean_2495_);
lean_ctor_set(v_reuseFailAlloc_2525_, 17, v_sstates_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, sizeof(void*)*18, v_inconsistent_2488_);
v___x_2518_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2518_);
v___x_2520_ = v___x_2477_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_mvarId_2475_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_st_ref_put(v___y_2451_, v___x_2520_);
v___x_2522_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2471_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v_as_x27_2449_ = v_tail_2464_;
v_b_2450_ = v___x_2465_;
goto _start;
}
else
{
return v___x_2522_;
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
lean_dec(v___x_2470_);
v_as_x27_2449_ = v_tail_2464_;
v_b_2450_ = v___x_2465_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2533_, v_b_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec(v_as_x27_2533_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2548_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2588_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2588_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2588_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_unbox(v_a_2560_);
lean_dec(v_a_2560_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v_toGoalState_2566_; lean_object* v_ematch_2567_; lean_object* v_delayedThmInsts_2568_; uint8_t v___x_2569_; 
v___x_2565_ = lean_st_ref_get(v_a_2548_);
v_toGoalState_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_ref(v_toGoalState_2566_);
lean_dec(v___x_2565_);
v_ematch_2567_ = lean_ctor_get(v_toGoalState_2566_, 13);
lean_inc_ref(v_ematch_2567_);
lean_dec_ref(v_toGoalState_2566_);
v_delayedThmInsts_2568_ = lean_ctor_get(v_ematch_2567_, 10);
lean_inc_ref(v_delayedThmInsts_2568_);
lean_dec_ref(v_ematch_2567_);
v___x_2569_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2568_);
lean_dec_ref(v_delayedThmInsts_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_del_object(v___x_2562_);
v___x_2570_ = lean_box(0);
v___x_2571_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2547_, v___x_2570_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2571_, 0);
lean_dec(v_unused_2579_);
v___x_2573_ = v___x_2571_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v___x_2571_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2570_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
else
{
return v___x_2571_;
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2580_);
v___x_2582_ = v___x_2562_;
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
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2584_);
v___x_2586_ = v___x_2562_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2559_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2559_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec(v_toPropagateDown_2597_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2611_, v_x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2614_, v_x_2615_, v_x_2616_);
lean_dec_ref(v_x_2616_);
lean_dec_ref(v_x_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2619_, v_x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2622_, v_x_2623_, v_x_2624_);
lean_dec_ref(v_x_2624_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2626_, lean_object* v_as_x27_2627_, lean_object* v_b_2628_, lean_object* v_a_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2627_, v_b_2628_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2642_, lean_object* v_as_x27_2643_, lean_object* v_b_2644_, lean_object* v_a_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2642_, v_as_x27_2643_, v_b_2644_, v_a_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v_as_x27_2643_);
lean_dec(v_as_2642_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2658_, lean_object* v_x_2659_, size_t v_x_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2659_, v_x_2660_, v_x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_){
_start:
{
size_t v_x_19995__boxed_2667_; lean_object* v_res_2668_; 
v_x_19995__boxed_2667_ = lean_unbox_usize(v_x_2665_);
lean_dec(v_x_2665_);
v_res_2668_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2663_, v_x_2664_, v_x_19995__boxed_2667_, v_x_2666_);
lean_dec_ref(v_x_2666_);
lean_dec_ref(v_x_2664_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, size_t v_x_2671_, lean_object* v_x_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2670_, v_x_2671_, v_x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v_x_2677_){
_start:
{
size_t v_x_20006__boxed_2678_; lean_object* v_res_2679_; 
v_x_20006__boxed_2678_ = lean_unbox_usize(v_x_2676_);
lean_dec(v_x_2676_);
v_res_2679_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2674_, v_x_2675_, v_x_20006__boxed_2678_, v_x_2677_);
lean_dec_ref(v_x_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2680_, lean_object* v_keys_2681_, lean_object* v_vals_2682_, lean_object* v_heq_2683_, lean_object* v_i_2684_, lean_object* v_k_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2681_, v_vals_2682_, v_i_2684_, v_k_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2687_, lean_object* v_keys_2688_, lean_object* v_vals_2689_, lean_object* v_heq_2690_, lean_object* v_i_2691_, lean_object* v_k_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2687_, v_keys_2688_, v_vals_2689_, v_heq_2690_, v_i_2691_, v_k_2692_);
lean_dec_ref(v_k_2692_);
lean_dec_ref(v_vals_2689_);
lean_dec_ref(v_keys_2688_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2694_, lean_object* v_keys_2695_, lean_object* v_vals_2696_, lean_object* v_i_2697_, lean_object* v_k_2698_){
_start:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = lean_array_get_size(v_keys_2695_);
v___x_2700_ = lean_nat_dec_lt(v_i_2697_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec_ref(v_k_2698_);
lean_dec(v_i_2697_);
v___x_2701_ = lean_box(0);
return v___x_2701_;
}
else
{
lean_object* v_k_x27_2702_; uint8_t v___x_2703_; 
v_k_x27_2702_ = lean_array_fget_borrowed(v_keys_2695_, v_i_2697_);
lean_inc(v_k_x27_2702_);
lean_inc_ref(v_k_2698_);
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2694_, v_k_2698_, v_k_x27_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_i_2697_, v___x_2704_);
lean_dec(v_i_2697_);
v_i_2697_ = v___x_2705_;
goto _start;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec_ref(v_k_2698_);
v___x_2707_ = lean_array_fget_borrowed(v_vals_2696_, v_i_2697_);
lean_dec(v_i_2697_);
lean_inc(v___x_2707_);
lean_inc(v_k_x27_2702_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_k_x27_2702_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2710_, lean_object* v_keys_2711_, lean_object* v_vals_2712_, lean_object* v_i_2713_, lean_object* v_k_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2710_, v_keys_2711_, v_vals_2712_, v_i_2713_, v_k_2714_);
lean_dec_ref(v_vals_2712_);
lean_dec_ref(v_keys_2711_);
lean_dec_ref(v___x_2710_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2716_, lean_object* v_x_2717_, size_t v_x_2718_, lean_object* v_x_2719_){
_start:
{
if (lean_obj_tag(v_x_2717_) == 0)
{
lean_object* v_es_2720_; lean_object* v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; lean_object* v_j_2724_; lean_object* v___x_2725_; 
v_es_2720_ = lean_ctor_get(v_x_2717_, 0);
lean_inc_ref(v_es_2720_);
lean_dec_ref_known(v_x_2717_, 1);
v___x_2721_ = lean_box(2);
v___x_2722_ = ((size_t)31ULL);
v___x_2723_ = lean_usize_land(v_x_2718_, v___x_2722_);
v_j_2724_ = lean_usize_to_nat(v___x_2723_);
v___x_2725_ = lean_array_get(v___x_2721_, v_es_2720_, v_j_2724_);
lean_dec(v_j_2724_);
lean_dec_ref(v_es_2720_);
switch(lean_obj_tag(v___x_2725_))
{
case 0:
{
lean_object* v_key_2726_; lean_object* v_val_2727_; uint8_t v___x_2728_; 
v_key_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_n(v_key_2726_, 2);
v_val_2727_ = lean_ctor_get(v___x_2725_, 1);
lean_inc(v_val_2727_);
lean_dec_ref_known(v___x_2725_, 2);
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2716_, v_x_2719_, v_key_2726_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
lean_dec(v_val_2727_);
lean_dec(v_key_2726_);
v___x_2729_ = lean_box(0);
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_key_2726_);
lean_ctor_set(v___x_2730_, 1, v_val_2727_);
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
case 1:
{
lean_object* v_node_2732_; size_t v___x_2733_; size_t v___x_2734_; 
v_node_2732_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_node_2732_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2733_ = ((size_t)5ULL);
v___x_2734_ = lean_usize_shift_right(v_x_2718_, v___x_2733_);
v_x_2717_ = v_node_2732_;
v_x_2718_ = v___x_2734_;
goto _start;
}
default: 
{
lean_object* v___x_2736_; 
lean_dec_ref(v_x_2719_);
v___x_2736_ = lean_box(0);
return v___x_2736_;
}
}
}
else
{
lean_object* v_ks_2737_; lean_object* v_vs_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_ks_2737_ = lean_ctor_get(v_x_2717_, 0);
lean_inc_ref(v_ks_2737_);
v_vs_2738_ = lean_ctor_get(v_x_2717_, 1);
lean_inc_ref(v_vs_2738_);
lean_dec_ref_known(v_x_2717_, 2);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2716_, v_ks_2737_, v_vs_2738_, v___x_2739_, v_x_2719_);
lean_dec_ref(v_vs_2738_);
lean_dec_ref(v_ks_2737_);
return v___x_2740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
size_t v_x_26131__boxed_2745_; lean_object* v_res_2746_; 
v_x_26131__boxed_2745_ = lean_unbox_usize(v_x_2743_);
lean_dec(v_x_2743_);
v_res_2746_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2741_, v_x_2742_, v_x_26131__boxed_2745_, v_x_2744_);
lean_dec_ref(v___x_2741_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
uint64_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
lean_inc_ref(v_x_2749_);
v___x_2750_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2747_, v_x_2749_);
v___x_2751_ = lean_uint64_to_usize(v___x_2750_);
lean_inc_ref(v_x_2748_);
v___x_2752_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2747_, v_x_2748_, v___x_2751_, v_x_2749_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2753_, v_x_2754_, v_x_2755_);
lean_dec_ref(v_x_2754_);
lean_dec_ref(v___x_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_){
_start:
{
lean_object* v_ks_2762_; lean_object* v_vs_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2787_; 
v_ks_2762_ = lean_ctor_get(v_x_2758_, 0);
v_vs_2763_ = lean_ctor_get(v_x_2758_, 1);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2765_ = v_x_2758_;
v_isShared_2766_ = v_isSharedCheck_2787_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_vs_2763_);
lean_inc(v_ks_2762_);
lean_dec(v_x_2758_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2787_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_array_get_size(v_ks_2762_);
v___x_2768_ = lean_nat_dec_lt(v_x_2759_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_x_2759_);
v___x_2769_ = lean_array_push(v_ks_2762_, v_x_2760_);
v___x_2770_ = lean_array_push(v_vs_2763_, v_x_2761_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2770_);
lean_ctor_set(v___x_2765_, 0, v___x_2769_);
v___x_2772_ = v___x_2765_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
lean_object* v_k_x27_2774_; uint8_t v___x_2775_; 
v_k_x27_2774_ = lean_array_fget_borrowed(v_ks_2762_, v_x_2759_);
lean_inc(v_k_x27_2774_);
lean_inc_ref(v_x_2760_);
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2757_, v_x_2760_, v_k_x27_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2777_; 
if (v_isShared_2766_ == 0)
{
v___x_2777_ = v___x_2765_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_ks_2762_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_vs_2763_);
v___x_2777_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = lean_nat_add(v_x_2759_, v___x_2778_);
lean_dec(v_x_2759_);
v_x_2758_ = v___x_2777_;
v_x_2759_ = v___x_2779_;
goto _start;
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2782_ = lean_array_fset(v_ks_2762_, v_x_2759_, v_x_2760_);
v___x_2783_ = lean_array_fset(v_vs_2763_, v_x_2759_, v_x_2761_);
lean_dec(v_x_2759_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2783_);
lean_ctor_set(v___x_2765_, 0, v___x_2782_);
v___x_2785_ = v___x_2765_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2788_, lean_object* v_x_2789_, lean_object* v_x_2790_, lean_object* v_x_2791_, lean_object* v_x_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2788_, v_x_2789_, v_x_2790_, v_x_2791_, v_x_2792_);
lean_dec_ref(v___x_2788_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2794_, lean_object* v_n_2795_, lean_object* v_k_2796_, lean_object* v_v_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2794_, v_n_2795_, v___x_2798_, v_k_2796_, v_v_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2800_, lean_object* v_n_2801_, lean_object* v_k_2802_, lean_object* v_v_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2800_, v_n_2801_, v_k_2802_, v_v_2803_);
lean_dec_ref(v___x_2800_);
return v_res_2804_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2806_, lean_object* v_x_2807_, size_t v_x_2808_, size_t v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_){
_start:
{
if (lean_obj_tag(v_x_2807_) == 0)
{
lean_object* v_es_2812_; size_t v___x_2813_; size_t v___x_2814_; lean_object* v_j_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_es_2812_ = lean_ctor_get(v_x_2807_, 0);
v___x_2813_ = ((size_t)31ULL);
v___x_2814_ = lean_usize_land(v_x_2808_, v___x_2813_);
v_j_2815_ = lean_usize_to_nat(v___x_2814_);
v___x_2816_ = lean_array_get_size(v_es_2812_);
v___x_2817_ = lean_nat_dec_lt(v_j_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_dec(v_j_2815_);
lean_dec(v_x_2811_);
lean_dec_ref(v_x_2810_);
return v_x_2807_;
}
else
{
lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2856_; 
lean_inc_ref(v_es_2812_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v_x_2807_, 0);
lean_dec(v_unused_2857_);
v___x_2819_ = v_x_2807_;
v_isShared_2820_ = v_isSharedCheck_2856_;
goto v_resetjp_2818_;
}
else
{
lean_dec(v_x_2807_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2856_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v_v_2821_; lean_object* v___x_2822_; lean_object* v_xs_x27_2823_; lean_object* v___y_2825_; 
v_v_2821_ = lean_array_fget(v_es_2812_, v_j_2815_);
v___x_2822_ = lean_box(0);
v_xs_x27_2823_ = lean_array_fset(v_es_2812_, v_j_2815_, v___x_2822_);
switch(lean_obj_tag(v_v_2821_))
{
case 0:
{
lean_object* v_key_2830_; lean_object* v_val_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2841_; 
v_key_2830_ = lean_ctor_get(v_v_2821_, 0);
v_val_2831_ = lean_ctor_get(v_v_2821_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_v_2821_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2833_ = v_v_2821_;
v_isShared_2834_ = v_isSharedCheck_2841_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_val_2831_);
lean_inc(v_key_2830_);
lean_dec(v_v_2821_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2841_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
uint8_t v___x_2835_; 
lean_inc(v_key_2830_);
lean_inc_ref(v_x_2810_);
v___x_2835_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2806_, v_x_2810_, v_key_2830_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2833_);
v___x_2836_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2830_, v_val_2831_, v_x_2810_, v_x_2811_);
v___x_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
v___y_2825_ = v___x_2837_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2839_; 
lean_dec(v_val_2831_);
lean_dec(v_key_2830_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 1, v_x_2811_);
lean_ctor_set(v___x_2833_, 0, v_x_2810_);
v___x_2839_ = v___x_2833_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_x_2810_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_x_2811_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v___y_2825_ = v___x_2839_;
goto v___jp_2824_;
}
}
}
}
case 1:
{
lean_object* v_node_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2854_; 
v_node_2842_ = lean_ctor_get(v_v_2821_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_v_2821_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2844_ = v_v_2821_;
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_node_2842_);
lean_dec(v_v_2821_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2854_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
size_t v___x_2846_; size_t v___x_2847_; size_t v___x_2848_; size_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2846_ = ((size_t)5ULL);
v___x_2847_ = lean_usize_shift_right(v_x_2808_, v___x_2846_);
v___x_2848_ = ((size_t)1ULL);
v___x_2849_ = lean_usize_add(v_x_2809_, v___x_2848_);
v___x_2850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2806_, v_node_2842_, v___x_2847_, v___x_2849_, v_x_2810_, v_x_2811_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2850_);
v___x_2852_ = v___x_2844_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
v___y_2825_ = v___x_2852_;
goto v___jp_2824_;
}
}
}
default: 
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_x_2810_);
lean_ctor_set(v___x_2855_, 1, v_x_2811_);
v___y_2825_ = v___x_2855_;
goto v___jp_2824_;
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = lean_array_fset(v_xs_x27_2823_, v_j_2815_, v___y_2825_);
lean_dec(v_j_2815_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2826_);
v___x_2828_ = v___x_2819_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
else
{
lean_object* v_ks_2858_; lean_object* v_vs_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2877_; 
v_ks_2858_ = lean_ctor_get(v_x_2807_, 0);
v_vs_2859_ = lean_ctor_get(v_x_2807_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_x_2807_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2861_ = v_x_2807_;
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_vs_2859_);
lean_inc(v_ks_2858_);
lean_dec(v_x_2807_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_ks_2858_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_vs_2859_);
v___x_2864_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v_newNode_2865_; size_t v___x_2866_; uint8_t v___x_2867_; 
v_newNode_2865_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2806_, v___x_2864_, v_x_2810_, v_x_2811_);
v___x_2866_ = ((size_t)7ULL);
v___x_2867_ = lean_usize_dec_le(v___x_2866_, v_x_2809_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2865_);
v___x_2869_ = lean_unsigned_to_nat(4u);
v___x_2870_ = lean_nat_dec_lt(v___x_2868_, v___x_2869_);
lean_dec(v___x_2868_);
if (v___x_2870_ == 0)
{
lean_object* v_ks_2871_; lean_object* v_vs_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_ks_2871_ = lean_ctor_get(v_newNode_2865_, 0);
lean_inc_ref(v_ks_2871_);
v_vs_2872_ = lean_ctor_get(v_newNode_2865_, 1);
lean_inc_ref(v_vs_2872_);
lean_dec_ref(v_newNode_2865_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2875_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2806_, v_x_2809_, v_ks_2871_, v_vs_2872_, v___x_2873_, v___x_2874_);
lean_dec_ref(v_vs_2872_);
lean_dec_ref(v_ks_2871_);
return v___x_2875_;
}
else
{
return v_newNode_2865_;
}
}
else
{
return v_newNode_2865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2878_, size_t v_depth_2879_, lean_object* v_keys_2880_, lean_object* v_vals_2881_, lean_object* v_i_2882_, lean_object* v_entries_2883_){
_start:
{
lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = lean_array_get_size(v_keys_2880_);
v___x_2885_ = lean_nat_dec_lt(v_i_2882_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec(v_i_2882_);
return v_entries_2883_;
}
else
{
lean_object* v_k_2886_; lean_object* v_v_2887_; uint64_t v___x_2888_; size_t v_h_2889_; size_t v___x_2890_; lean_object* v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; size_t v_h_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_k_2886_ = lean_array_fget_borrowed(v_keys_2880_, v_i_2882_);
v_v_2887_ = lean_array_fget_borrowed(v_vals_2881_, v_i_2882_);
lean_inc_n(v_k_2886_, 2);
v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2878_, v_k_2886_);
v_h_2889_ = lean_uint64_to_usize(v___x_2888_);
v___x_2890_ = ((size_t)5ULL);
v___x_2891_ = lean_unsigned_to_nat(1u);
v___x_2892_ = ((size_t)1ULL);
v___x_2893_ = lean_usize_sub(v_depth_2879_, v___x_2892_);
v___x_2894_ = lean_usize_mul(v___x_2890_, v___x_2893_);
v_h_2895_ = lean_usize_shift_right(v_h_2889_, v___x_2894_);
v___x_2896_ = lean_nat_add(v_i_2882_, v___x_2891_);
lean_dec(v_i_2882_);
lean_inc(v_v_2887_);
v___x_2897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2878_, v_entries_2883_, v_h_2895_, v_depth_2879_, v_k_2886_, v_v_2887_);
v_i_2882_ = v___x_2896_;
v_entries_2883_ = v___x_2897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2899_, lean_object* v_depth_2900_, lean_object* v_keys_2901_, lean_object* v_vals_2902_, lean_object* v_i_2903_, lean_object* v_entries_2904_){
_start:
{
size_t v_depth_boxed_2905_; lean_object* v_res_2906_; 
v_depth_boxed_2905_ = lean_unbox_usize(v_depth_2900_);
lean_dec(v_depth_2900_);
v_res_2906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2899_, v_depth_boxed_2905_, v_keys_2901_, v_vals_2902_, v_i_2903_, v_entries_2904_);
lean_dec_ref(v_vals_2902_);
lean_dec_ref(v_keys_2901_);
lean_dec_ref(v___x_2899_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_){
_start:
{
size_t v_x_26285__boxed_2913_; size_t v_x_26286__boxed_2914_; lean_object* v_res_2915_; 
v_x_26285__boxed_2913_ = lean_unbox_usize(v_x_2909_);
lean_dec(v_x_2909_);
v_x_26286__boxed_2914_ = lean_unbox_usize(v_x_2910_);
lean_dec(v_x_2910_);
v_res_2915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2907_, v_x_2908_, v_x_26285__boxed_2913_, v_x_26286__boxed_2914_, v_x_2911_, v_x_2912_);
lean_dec_ref(v___x_2907_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
uint64_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
lean_inc_ref(v_x_2918_);
v___x_2920_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2916_, v_x_2918_);
v___x_2921_ = lean_uint64_to_usize(v___x_2920_);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2916_, v_x_2917_, v___x_2921_, v___x_2922_, v_x_2918_, v_x_2919_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_, lean_object* v_x_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2924_, v_x_2925_, v_x_2926_, v_x_2927_);
lean_dec_ref(v___x_2924_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2933_, lean_object* v_rootNew_2934_, uint8_t v_a_2935_, lean_object* v_a_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_snd_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3129_; 
v_snd_2944_ = lean_ctor_get(v_a_2936_, 1);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_a_2936_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_a_2936_, 0);
lean_dec(v_unused_3130_);
v___x_2946_ = v_a_2936_;
v_isShared_2947_ = v_isSharedCheck_3129_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snd_2944_);
lean_dec(v_a_2936_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3129_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_st_ref_get(v___y_2937_);
lean_inc(v_snd_2944_);
v___x_2950_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2949_, v_snd_2944_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___x_2949_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3120_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_3120_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3120_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_self_2955_; lean_object* v_next_2956_; lean_object* v_congr_2957_; lean_object* v_target_x3f_2958_; lean_object* v_proof_x3f_2959_; uint8_t v_flipped_2960_; lean_object* v_size_2961_; uint8_t v_interpreted_2962_; uint8_t v_ctor_2963_; uint8_t v_hasLambdas_2964_; uint8_t v_heqProofs_2965_; lean_object* v_idx_2966_; lean_object* v_generation_2967_; lean_object* v_mt_2968_; lean_object* v_sTerms_2969_; uint8_t v_funCC_2970_; lean_object* v_ematchDiagSource_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3118_; 
v_self_2955_ = lean_ctor_get(v_a_2951_, 0);
v_next_2956_ = lean_ctor_get(v_a_2951_, 1);
v_congr_2957_ = lean_ctor_get(v_a_2951_, 3);
v_target_x3f_2958_ = lean_ctor_get(v_a_2951_, 4);
v_proof_x3f_2959_ = lean_ctor_get(v_a_2951_, 5);
v_flipped_2960_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12);
v_size_2961_ = lean_ctor_get(v_a_2951_, 6);
v_interpreted_2962_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12 + 1);
v_ctor_2963_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12 + 2);
v_hasLambdas_2964_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12 + 3);
v_heqProofs_2965_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12 + 4);
v_idx_2966_ = lean_ctor_get(v_a_2951_, 7);
v_generation_2967_ = lean_ctor_get(v_a_2951_, 8);
v_mt_2968_ = lean_ctor_get(v_a_2951_, 9);
v_sTerms_2969_ = lean_ctor_get(v_a_2951_, 10);
v_funCC_2970_ = lean_ctor_get_uint8(v_a_2951_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2971_ = lean_ctor_get(v_a_2951_, 11);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_2951_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v_a_2951_, 2);
lean_dec(v_unused_3119_);
v___x_2973_ = v_a_2951_;
v_isShared_2974_ = v_isSharedCheck_3118_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_ematchDiagSource_2971_);
lean_inc(v_sTerms_2969_);
lean_inc(v_mt_2968_);
lean_inc(v_generation_2967_);
lean_inc(v_idx_2966_);
lean_inc(v_size_2961_);
lean_inc(v_proof_x3f_2959_);
lean_inc(v_target_x3f_2958_);
lean_inc(v_congr_2957_);
lean_inc(v_next_2956_);
lean_inc(v_self_2955_);
lean_dec(v_a_2951_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3118_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2991_; 
lean_inc(v_ematchDiagSource_2971_);
lean_inc(v_sTerms_2969_);
lean_inc(v_mt_2968_);
lean_inc(v_generation_2967_);
lean_inc(v_idx_2966_);
lean_inc(v_size_2961_);
lean_inc(v_proof_x3f_2959_);
lean_inc(v_target_x3f_2958_);
lean_inc_ref(v_rootNew_2934_);
lean_inc_ref(v_next_2956_);
lean_inc_ref(v_self_2955_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v_rootNew_2934_);
v___x_2991_ = v___x_2973_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_self_2955_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_next_2956_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_rootNew_2934_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_congr_2957_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v_target_x3f_2958_);
lean_ctor_set(v_reuseFailAlloc_3117_, 5, v_proof_x3f_2959_);
lean_ctor_set(v_reuseFailAlloc_3117_, 6, v_size_2961_);
lean_ctor_set(v_reuseFailAlloc_3117_, 7, v_idx_2966_);
lean_ctor_set(v_reuseFailAlloc_3117_, 8, v_generation_2967_);
lean_ctor_set(v_reuseFailAlloc_3117_, 9, v_mt_2968_);
lean_ctor_set(v_reuseFailAlloc_3117_, 10, v_sTerms_2969_);
lean_ctor_set(v_reuseFailAlloc_3117_, 11, v_ematchDiagSource_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12, v_flipped_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12 + 1, v_interpreted_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12 + 2, v_ctor_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12 + 3, v_hasLambdas_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12 + 4, v_heqProofs_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*12 + 5, v_funCC_2970_);
v___x_2991_ = v_reuseFailAlloc_3117_;
goto v_reusejp_2990_;
}
v___jp_2975_:
{
size_t v___x_2976_; size_t v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_ptr_addr(v_next_2956_);
v___x_2977_ = lean_ptr_addr(v_lhs_2933_);
v___x_2978_ = lean_usize_dec_eq(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2980_; 
lean_del_object(v___x_2953_);
lean_dec(v_snd_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_next_2956_);
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2980_ = v___x_2946_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_next_2956_);
v___x_2980_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
v_a_2936_ = v___x_2980_;
goto _start;
}
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_rootNew_2934_);
v___x_2983_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2983_);
v___x_2985_ = v___x_2946_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_snd_2944_);
v___x_2985_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2985_);
v___x_2987_ = v___x_2953_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; 
lean_inc_ref(v___x_2991_);
lean_inc_ref(v_self_2955_);
v___x_2992_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2955_, v___x_2991_, v___y_2937_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec_ref_known(v___x_2992_, 1);
if (v_a_2935_ == 0)
{
lean_dec_ref(v___x_2991_);
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_self_2955_);
goto v___jp_2975_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2993_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2994_ = lean_unsigned_to_nat(3u);
v___x_2995_ = l_Lean_Expr_isAppOfArity(v_self_2955_, v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v___x_2991_);
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_self_2955_);
goto v___jp_2975_;
}
else
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2991_);
lean_dec_ref(v___x_2991_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v_toGoalState_2998_; lean_object* v_enodeMap_2999_; lean_object* v_congrTable_3000_; lean_object* v___x_3001_; 
v___x_2997_ = lean_st_ref_get(v___y_2937_);
v_toGoalState_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_toGoalState_2998_);
lean_dec(v___x_2997_);
v_enodeMap_2999_ = lean_ctor_get(v_toGoalState_2998_, 1);
lean_inc_ref(v_enodeMap_2999_);
v_congrTable_3000_ = lean_ctor_get(v_toGoalState_2998_, 4);
lean_inc_ref(v_congrTable_3000_);
lean_dec_ref(v_toGoalState_2998_);
lean_inc_ref(v_self_2955_);
v___x_3001_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2999_, v_congrTable_3000_, v_self_2955_);
lean_dec_ref(v_congrTable_3000_);
lean_dec_ref(v_enodeMap_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_self_2955_);
goto v___jp_2975_;
}
else
{
lean_object* v_val_3002_; lean_object* v_fst_3003_; lean_object* v___x_3004_; 
v_val_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v_fst_3003_ = lean_ctor_get(v_val_3002_, 0);
lean_inc(v_fst_3003_);
lean_dec(v_val_3002_);
v___x_3004_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3003_, v___y_2938_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; uint8_t v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = lean_unbox(v_a_3005_);
lean_dec(v_a_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v_toGoalState_3008_; lean_object* v_mvarId_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3100_; 
v___x_3007_ = lean_st_ref_take(v___y_2937_);
v_toGoalState_3008_ = lean_ctor_get(v___x_3007_, 0);
v_mvarId_3009_ = lean_ctor_get(v___x_3007_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3011_ = v___x_3007_;
v_isShared_3012_ = v_isSharedCheck_3100_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_mvarId_3009_);
lean_inc(v_toGoalState_3008_);
lean_dec(v___x_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3100_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v_nextDeclIdx_3013_; lean_object* v_enodeMap_3014_; lean_object* v_exprs_3015_; lean_object* v_parents_3016_; lean_object* v_congrTable_3017_; lean_object* v_appMap_3018_; lean_object* v_indicesFound_3019_; lean_object* v_toProcess_3020_; lean_object* v_internalizing_3021_; uint8_t v_inconsistent_3022_; lean_object* v_nextIdx_3023_; lean_object* v_newRawFacts_3024_; lean_object* v_facts_3025_; lean_object* v_extThms_3026_; lean_object* v_ematch_3027_; lean_object* v_inj_3028_; lean_object* v_split_3029_; lean_object* v_clean_3030_; lean_object* v_sstates_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3099_; 
v_nextDeclIdx_3013_ = lean_ctor_get(v_toGoalState_3008_, 0);
v_enodeMap_3014_ = lean_ctor_get(v_toGoalState_3008_, 1);
v_exprs_3015_ = lean_ctor_get(v_toGoalState_3008_, 2);
v_parents_3016_ = lean_ctor_get(v_toGoalState_3008_, 3);
v_congrTable_3017_ = lean_ctor_get(v_toGoalState_3008_, 4);
v_appMap_3018_ = lean_ctor_get(v_toGoalState_3008_, 5);
v_indicesFound_3019_ = lean_ctor_get(v_toGoalState_3008_, 6);
v_toProcess_3020_ = lean_ctor_get(v_toGoalState_3008_, 7);
v_internalizing_3021_ = lean_ctor_get(v_toGoalState_3008_, 8);
v_inconsistent_3022_ = lean_ctor_get_uint8(v_toGoalState_3008_, sizeof(void*)*18);
v_nextIdx_3023_ = lean_ctor_get(v_toGoalState_3008_, 9);
v_newRawFacts_3024_ = lean_ctor_get(v_toGoalState_3008_, 10);
v_facts_3025_ = lean_ctor_get(v_toGoalState_3008_, 11);
v_extThms_3026_ = lean_ctor_get(v_toGoalState_3008_, 12);
v_ematch_3027_ = lean_ctor_get(v_toGoalState_3008_, 13);
v_inj_3028_ = lean_ctor_get(v_toGoalState_3008_, 14);
v_split_3029_ = lean_ctor_get(v_toGoalState_3008_, 15);
v_clean_3030_ = lean_ctor_get(v_toGoalState_3008_, 16);
v_sstates_3031_ = lean_ctor_get(v_toGoalState_3008_, 17);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_toGoalState_3008_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3033_ = v_toGoalState_3008_;
v_isShared_3034_ = v_isSharedCheck_3099_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_sstates_3031_);
lean_inc(v_clean_3030_);
lean_inc(v_split_3029_);
lean_inc(v_inj_3028_);
lean_inc(v_ematch_3027_);
lean_inc(v_extThms_3026_);
lean_inc(v_facts_3025_);
lean_inc(v_newRawFacts_3024_);
lean_inc(v_nextIdx_3023_);
lean_inc(v_internalizing_3021_);
lean_inc(v_toProcess_3020_);
lean_inc(v_indicesFound_3019_);
lean_inc(v_appMap_3018_);
lean_inc(v_congrTable_3017_);
lean_inc(v_parents_3016_);
lean_inc(v_exprs_3015_);
lean_inc(v_enodeMap_3014_);
lean_inc(v_nextDeclIdx_3013_);
lean_dec(v_toGoalState_3008_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3099_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3035_ = lean_box(0);
lean_inc_ref(v_self_2955_);
v___x_3036_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3014_, v_congrTable_3017_, v_self_2955_, v___x_3035_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 4, v___x_3036_);
v___x_3038_ = v___x_3033_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_nextDeclIdx_3013_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_enodeMap_3014_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_exprs_3015_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_parents_3016_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_appMap_3018_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_indicesFound_3019_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_toProcess_3020_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_internalizing_3021_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_nextIdx_3023_);
lean_ctor_set(v_reuseFailAlloc_3098_, 10, v_newRawFacts_3024_);
lean_ctor_set(v_reuseFailAlloc_3098_, 11, v_facts_3025_);
lean_ctor_set(v_reuseFailAlloc_3098_, 12, v_extThms_3026_);
lean_ctor_set(v_reuseFailAlloc_3098_, 13, v_ematch_3027_);
lean_ctor_set(v_reuseFailAlloc_3098_, 14, v_inj_3028_);
lean_ctor_set(v_reuseFailAlloc_3098_, 15, v_split_3029_);
lean_ctor_set(v_reuseFailAlloc_3098_, 16, v_clean_3030_);
lean_ctor_set(v_reuseFailAlloc_3098_, 17, v_sstates_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*18, v_inconsistent_3022_);
v___x_3038_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3038_);
v___x_3040_ = v___x_3011_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_mvarId_3009_);
v___x_3040_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = lean_st_ref_put(v___y_2937_, v___x_3040_);
lean_inc_ref(v_rootNew_2934_);
lean_inc_ref(v_next_2956_);
lean_inc_ref_n(v_self_2955_, 3);
v___x_3042_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3042_, 0, v_self_2955_);
lean_ctor_set(v___x_3042_, 1, v_next_2956_);
lean_ctor_set(v___x_3042_, 2, v_rootNew_2934_);
lean_ctor_set(v___x_3042_, 3, v_self_2955_);
lean_ctor_set(v___x_3042_, 4, v_target_x3f_2958_);
lean_ctor_set(v___x_3042_, 5, v_proof_x3f_2959_);
lean_ctor_set(v___x_3042_, 6, v_size_2961_);
lean_ctor_set(v___x_3042_, 7, v_idx_2966_);
lean_ctor_set(v___x_3042_, 8, v_generation_2967_);
lean_ctor_set(v___x_3042_, 9, v_mt_2968_);
lean_ctor_set(v___x_3042_, 10, v_sTerms_2969_);
lean_ctor_set(v___x_3042_, 11, v_ematchDiagSource_2971_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12, v_flipped_2960_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12 + 1, v_interpreted_2962_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12 + 2, v_ctor_2963_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12 + 3, v_hasLambdas_2964_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12 + 4, v_heqProofs_2965_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*12 + 5, v_funCC_2970_);
v___x_3043_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2955_, v___x_3042_, v___y_2937_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec_ref_known(v___x_3043_, 1);
v___x_3044_ = lean_st_ref_get(v___y_2937_);
lean_inc(v_fst_3003_);
v___x_3045_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3044_, v_fst_3003_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___x_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v_self_3047_; lean_object* v_next_3048_; lean_object* v_root_3049_; lean_object* v_target_x3f_3050_; lean_object* v_proof_x3f_3051_; uint8_t v_flipped_3052_; lean_object* v_size_3053_; uint8_t v_interpreted_3054_; uint8_t v_ctor_3055_; uint8_t v_hasLambdas_3056_; uint8_t v_heqProofs_3057_; lean_object* v_idx_3058_; lean_object* v_generation_3059_; lean_object* v_mt_3060_; lean_object* v_sTerms_3061_; uint8_t v_funCC_3062_; lean_object* v_ematchDiagSource_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3079_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v_self_3047_ = lean_ctor_get(v_a_3046_, 0);
v_next_3048_ = lean_ctor_get(v_a_3046_, 1);
v_root_3049_ = lean_ctor_get(v_a_3046_, 2);
v_target_x3f_3050_ = lean_ctor_get(v_a_3046_, 4);
v_proof_x3f_3051_ = lean_ctor_get(v_a_3046_, 5);
v_flipped_3052_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12);
v_size_3053_ = lean_ctor_get(v_a_3046_, 6);
v_interpreted_3054_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12 + 1);
v_ctor_3055_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12 + 2);
v_hasLambdas_3056_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12 + 3);
v_heqProofs_3057_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12 + 4);
v_idx_3058_ = lean_ctor_get(v_a_3046_, 7);
v_generation_3059_ = lean_ctor_get(v_a_3046_, 8);
v_mt_3060_ = lean_ctor_get(v_a_3046_, 9);
v_sTerms_3061_ = lean_ctor_get(v_a_3046_, 10);
v_funCC_3062_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3063_ = lean_ctor_get(v_a_3046_, 11);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_a_3046_);
if (v_isSharedCheck_3079_ == 0)
{
lean_object* v_unused_3080_; 
v_unused_3080_ = lean_ctor_get(v_a_3046_, 3);
lean_dec(v_unused_3080_);
v___x_3065_ = v_a_3046_;
v_isShared_3066_ = v_isSharedCheck_3079_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_ematchDiagSource_3063_);
lean_inc(v_sTerms_3061_);
lean_inc(v_mt_3060_);
lean_inc(v_generation_3059_);
lean_inc(v_idx_3058_);
lean_inc(v_size_3053_);
lean_inc(v_proof_x3f_3051_);
lean_inc(v_target_x3f_3050_);
lean_inc(v_root_3049_);
lean_inc(v_next_3048_);
lean_inc(v_self_3047_);
lean_dec(v_a_3046_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3079_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 3, v_self_2955_);
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_self_3047_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_next_3048_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v_root_3049_);
lean_ctor_set(v_reuseFailAlloc_3078_, 3, v_self_2955_);
lean_ctor_set(v_reuseFailAlloc_3078_, 4, v_target_x3f_3050_);
lean_ctor_set(v_reuseFailAlloc_3078_, 5, v_proof_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3078_, 6, v_size_3053_);
lean_ctor_set(v_reuseFailAlloc_3078_, 7, v_idx_3058_);
lean_ctor_set(v_reuseFailAlloc_3078_, 8, v_generation_3059_);
lean_ctor_set(v_reuseFailAlloc_3078_, 9, v_mt_3060_);
lean_ctor_set(v_reuseFailAlloc_3078_, 10, v_sTerms_3061_);
lean_ctor_set(v_reuseFailAlloc_3078_, 11, v_ematchDiagSource_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12, v_flipped_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12 + 1, v_interpreted_3054_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12 + 2, v_ctor_3055_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12 + 3, v_hasLambdas_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12 + 4, v_heqProofs_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3078_, sizeof(void*)*12 + 5, v_funCC_3062_);
v___x_3068_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3003_, v___x_3068_, v___y_2937_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref_known(v___x_3069_, 1);
goto v___jp_2975_;
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v_next_2956_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_fst_3003_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3081_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3045_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3045_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_fst_3003_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3089_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3043_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3043_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
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
lean_dec(v_fst_3003_);
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_self_2955_);
goto v___jp_2975_;
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_fst_3003_);
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3101_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3004_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3004_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_self_2955_);
goto v___jp_2975_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v___x_2991_);
lean_dec(v_ematchDiagSource_2971_);
lean_dec(v_sTerms_2969_);
lean_dec(v_mt_2968_);
lean_dec(v_generation_2967_);
lean_dec(v_idx_2966_);
lean_dec(v_size_2961_);
lean_dec(v_proof_x3f_2959_);
lean_dec(v_target_x3f_2958_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3109_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2992_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2992_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3121_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_2950_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_2950_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3131_, lean_object* v_rootNew_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_a_26469__boxed_3142_; lean_object* v_res_3143_; 
v_a_26469__boxed_3142_ = lean_unbox(v_a_3133_);
v_res_3143_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3131_, v_rootNew_3132_, v_a_26469__boxed_3142_, v_a_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v_lhs_3131_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3144_, lean_object* v_rootNew_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3145_, v_a_3150_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3159_ = lean_box(0);
lean_inc_ref(v_lhs_3144_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v_lhs_3144_);
v___x_3161_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
v___x_3162_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3144_, v_rootNew_3145_, v___x_3161_, v___x_3160_, v_a_3146_, v_a_3150_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
lean_dec_ref(v_lhs_3144_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3176_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v_fst_3167_; 
v_fst_3167_ = lean_ctor_get(v_a_3163_, 0);
lean_inc(v_fst_3167_);
lean_dec(v_a_3163_);
if (lean_obj_tag(v_fst_3167_) == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_box(0);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3168_);
v___x_3170_ = v___x_3165_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
else
{
lean_object* v_val_3172_; lean_object* v___x_3174_; 
v_val_3172_ = lean_ctor_get(v_fst_3167_, 0);
lean_inc(v_val_3172_);
lean_dec_ref_known(v_fst_3167_, 1);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v_val_3172_);
v___x_3174_ = v___x_3165_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_val_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3162_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3162_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v_rootNew_3145_);
lean_dec_ref(v_lhs_3144_);
v_a_3185_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3157_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3157_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3193_, lean_object* v_rootNew_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3193_, v_rootNew_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec(v_a_3195_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3207_, lean_object* v_00_u03b2_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3207_, v_x_3209_, v_x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3212_, lean_object* v_00_u03b2_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3212_, v_00_u03b2_3213_, v_x_3214_, v_x_3215_);
lean_dec_ref(v_x_3214_);
lean_dec_ref(v___x_3212_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3217_, lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3217_, v_x_3219_, v_x_3220_, v_x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3223_, v_00_u03b2_3224_, v_x_3225_, v_x_3226_, v_x_3227_);
lean_dec_ref(v___x_3223_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3229_, lean_object* v_rootNew_3230_, uint8_t v_a_3231_, lean_object* v_inst_3232_, lean_object* v_a_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3229_, v_rootNew_3230_, v_a_3231_, v_a_3233_, v___y_3234_, v___y_3238_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3246_, lean_object* v_rootNew_3247_, lean_object* v_a_3248_, lean_object* v_inst_3249_, lean_object* v_a_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v_a_26854__boxed_3262_; lean_object* v_res_3263_; 
v_a_26854__boxed_3262_ = lean_unbox(v_a_3248_);
v_res_3263_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3246_, v_rootNew_3247_, v_a_26854__boxed_3262_, v_inst_3249_, v_a_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v_lhs_3246_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, size_t v_x_3267_, lean_object* v_x_3268_){
_start:
{
lean_object* v___x_3269_; 
lean_inc_ref(v_x_3266_);
v___x_3269_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3264_, v_x_3266_, v_x_3267_, v_x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
size_t v_x_26897__boxed_3275_; lean_object* v_res_3276_; 
v_x_26897__boxed_3275_ = lean_unbox_usize(v_x_3273_);
lean_dec(v_x_3273_);
v_res_3276_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3270_, v_00_u03b2_3271_, v_x_3272_, v_x_26897__boxed_3275_, v_x_3274_);
lean_dec_ref(v_x_3272_);
lean_dec_ref(v___x_3270_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3277_, lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, size_t v_x_3280_, size_t v_x_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3277_, v_x_3279_, v_x_3280_, v_x_3281_, v_x_3282_, v_x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3285_, lean_object* v_00_u03b2_3286_, lean_object* v_x_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
size_t v_x_26911__boxed_3292_; size_t v_x_26912__boxed_3293_; lean_object* v_res_3294_; 
v_x_26911__boxed_3292_ = lean_unbox_usize(v_x_3288_);
lean_dec(v_x_3288_);
v_x_26912__boxed_3293_ = lean_unbox_usize(v_x_3289_);
lean_dec(v_x_3289_);
v_res_3294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3285_, v_00_u03b2_3286_, v_x_3287_, v_x_26911__boxed_3292_, v_x_26912__boxed_3293_, v_x_3290_, v_x_3291_);
lean_dec_ref(v___x_3285_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3295_, lean_object* v_00_u03b2_3296_, lean_object* v_keys_3297_, lean_object* v_vals_3298_, lean_object* v_heq_3299_, lean_object* v_i_3300_, lean_object* v_k_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3295_, v_keys_3297_, v_vals_3298_, v_i_3300_, v_k_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_keys_3305_, lean_object* v_vals_3306_, lean_object* v_heq_3307_, lean_object* v_i_3308_, lean_object* v_k_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3303_, v_00_u03b2_3304_, v_keys_3305_, v_vals_3306_, v_heq_3307_, v_i_3308_, v_k_3309_);
lean_dec_ref(v_vals_3306_);
lean_dec_ref(v_keys_3305_);
lean_dec_ref(v___x_3303_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3311_, lean_object* v_00_u03b2_3312_, lean_object* v_n_3313_, lean_object* v_k_3314_, lean_object* v_v_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3311_, v_n_3313_, v_k_3314_, v_v_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3317_, lean_object* v_00_u03b2_3318_, lean_object* v_n_3319_, lean_object* v_k_3320_, lean_object* v_v_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3317_, v_00_u03b2_3318_, v_n_3319_, v_k_3320_, v_v_3321_);
lean_dec_ref(v___x_3317_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3323_, lean_object* v_00_u03b2_3324_, size_t v_depth_3325_, lean_object* v_keys_3326_, lean_object* v_vals_3327_, lean_object* v_heq_3328_, lean_object* v_i_3329_, lean_object* v_entries_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3323_, v_depth_3325_, v_keys_3326_, v_vals_3327_, v_i_3329_, v_entries_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3332_, lean_object* v_00_u03b2_3333_, lean_object* v_depth_3334_, lean_object* v_keys_3335_, lean_object* v_vals_3336_, lean_object* v_heq_3337_, lean_object* v_i_3338_, lean_object* v_entries_3339_){
_start:
{
size_t v_depth_boxed_3340_; lean_object* v_res_3341_; 
v_depth_boxed_3340_ = lean_unbox_usize(v_depth_3334_);
lean_dec(v_depth_3334_);
v_res_3341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3332_, v_00_u03b2_3333_, v_depth_boxed_3340_, v_keys_3335_, v_vals_3336_, v_heq_3337_, v_i_3338_, v_entries_3339_);
lean_dec_ref(v_vals_3336_);
lean_dec_ref(v_keys_3335_);
lean_dec_ref(v___x_3332_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3342_, lean_object* v_00_u03b2_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3342_, v_x_3344_, v_x_3345_, v_x_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3349_, lean_object* v_00_u03b2_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3349_, v_00_u03b2_3350_, v_x_3351_, v_x_3352_, v_x_3353_, v_x_3354_);
lean_dec_ref(v___x_3349_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
if (lean_obj_tag(v_as_x27_3356_) == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_b_3357_);
return v___x_3369_;
}
else
{
lean_object* v_head_3370_; lean_object* v_tail_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_head_3370_ = lean_ctor_get(v_as_x27_3356_, 0);
v_tail_3371_ = lean_ctor_get(v_as_x27_3356_, 1);
v___x_3372_ = lean_box(0);
lean_inc(v_head_3370_);
v___x_3373_ = l_Lean_Meta_Grind_propagateUp(v_head_3370_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_dec_ref_known(v___x_3373_, 1);
v_as_x27_3356_ = v_tail_3371_;
v_b_3357_ = v___x_3372_;
goto _start;
}
else
{
return v___x_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3375_, lean_object* v_b_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3375_, v_b_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec(v_as_x27_3375_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3389_, lean_object* v_b_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
if (lean_obj_tag(v_as_x27_3389_) == 0)
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3402_, 0, v_b_3390_);
return v___x_3402_;
}
else
{
lean_object* v_head_3403_; lean_object* v_tail_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_head_3403_ = lean_ctor_get(v_as_x27_3389_, 0);
v_tail_3404_ = lean_ctor_get(v_as_x27_3389_, 1);
v___x_3405_ = lean_box(0);
lean_inc(v_head_3403_);
v___x_3406_ = l_Lean_Meta_Grind_propagateDown(v_head_3403_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v_as_x27_3389_ = v_tail_3404_;
v_b_3390_ = v___x_3405_;
goto _start;
}
else
{
return v___x_3406_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3408_, lean_object* v_b_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3408_, v_b_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v_as_x27_3408_);
return v_res_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_cls_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3426_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3427_ = l_Lean_Name_append(v___x_3426_, v_cls_3425_);
return v___x_3427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3440_, uint8_t v_isHEq_3441_, lean_object* v_lhs_3442_, lean_object* v_rhs_3443_, lean_object* v_lhsNode_3444_, lean_object* v_rhsNode_3445_, lean_object* v_lhsRoot_3446_, lean_object* v_rhsRoot_3447_, uint8_t v_flipped_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; uint8_t v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; uint8_t v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; uint8_t v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; uint8_t v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v_toCold_3698_; lean_object* v_options_3699_; lean_object* v_inheritedTraceOptions_3700_; uint8_t v_hasTrace_3701_; lean_object* v_cls_3702_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v_fns_u2082_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_fns_u2081_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; 
v_toCold_3698_ = lean_ctor_get(v_a_3457_, 0);
v_options_3699_ = lean_ctor_get(v_toCold_3698_, 2);
v_inheritedTraceOptions_3700_ = lean_ctor_get(v_toCold_3698_, 11);
v_hasTrace_3701_ = lean_ctor_get_uint8(v_options_3699_, sizeof(void*)*1);
v_cls_3702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3701_ == 0)
{
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
v___y_3828_ = v_a_3455_;
v___y_3829_ = v_a_3456_;
v___y_3830_ = v_a_3457_;
v___y_3831_ = v_a_3458_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3903_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3700_, v_options_3699_, v___x_3902_);
if (v___x_3903_ == 0)
{
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
v___y_3828_ = v_a_3455_;
v___y_3829_ = v_a_3456_;
v___y_3830_ = v_a_3457_;
v___y_3831_ = v_a_3458_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Meta_Grind_updateLastTag(v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v___x_3905_; 
lean_dec_ref_known(v___x_3904_, 1);
lean_inc_ref(v_lhs_3442_);
v___x_3905_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3442_, v_a_3449_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
lean_inc_ref(v_rhs_3443_);
v___x_3907_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3443_, v_a_3449_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v_a_3906_);
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3910_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v_a_3908_);
v___x_3914_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3702_, v___x_3913_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_dec_ref_known(v___x_3914_, 1);
v___y_3822_ = v_a_3449_;
v___y_3823_ = v_a_3450_;
v___y_3824_ = v_a_3451_;
v___y_3825_ = v_a_3452_;
v___y_3826_ = v_a_3453_;
v___y_3827_ = v_a_3454_;
v___y_3828_ = v_a_3455_;
v___y_3829_ = v_a_3456_;
v___y_3830_ = v_a_3457_;
v___y_3831_ = v_a_3458_;
goto v___jp_3821_;
}
else
{
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhsNode_3444_);
lean_dec_ref(v_rhs_3443_);
lean_dec_ref(v_lhs_3442_);
lean_dec_ref(v_proof_3440_);
return v___x_3914_;
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_a_3906_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhsNode_3444_);
lean_dec_ref(v_rhs_3443_);
lean_dec_ref(v_lhs_3442_);
lean_dec_ref(v_proof_3440_);
v_a_3915_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3907_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3907_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhsNode_3444_);
lean_dec_ref(v_rhs_3443_);
lean_dec_ref(v_lhs_3442_);
lean_dec_ref(v_proof_3440_);
v_a_3923_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3905_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3905_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhsNode_3444_);
lean_dec_ref(v_rhs_3443_);
lean_dec_ref(v_lhs_3442_);
lean_dec_ref(v_proof_3440_);
return v___x_3904_;
}
}
}
v___jp_3460_:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3467_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3503_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3503_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3503_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
uint8_t v___x_3482_; 
v___x_3482_ = lean_unbox(v_a_3478_);
lean_dec(v_a_3478_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_del_object(v___x_3480_);
v___x_3483_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3461_);
lean_dec(v___y_3461_);
v___x_3484_ = lean_box(0);
v___x_3485_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3483_, v___x_3484_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___x_3483_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref_known(v___x_3485_, 1);
v___x_3486_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3463_, v___x_3484_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref_known(v___x_3486_, 1);
v___x_3487_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3464_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3464_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref_known(v___x_3487_, 1);
v___x_3488_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3462_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3497_; 
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3488_, 0);
lean_dec(v_unused_3498_);
v___x_3490_ = v___x_3488_;
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v___x_3488_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_Expr_isTrue(v___y_3465_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3494_; 
lean_dec(v___y_3463_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3484_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3484_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
else
{
lean_object* v___x_3496_; 
lean_del_object(v___x_3490_);
v___x_3496_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3463_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3463_);
return v___x_3496_;
}
}
}
else
{
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3463_);
return v___x_3488_;
}
}
else
{
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
return v___x_3487_;
}
}
else
{
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
return v___x_3486_;
}
}
else
{
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
return v___x_3485_;
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec(v___y_3461_);
v___x_3499_ = lean_box(0);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3499_);
v___x_3501_ = v___x_3480_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec(v___y_3461_);
v_a_3504_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3477_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3477_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
v___jp_3512_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_inc_ref(v___y_3520_);
v___x_3549_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3549_, 0, v___y_3520_);
lean_ctor_set(v___x_3549_, 1, v___y_3519_);
lean_ctor_set(v___x_3549_, 2, v___y_3535_);
lean_ctor_set(v___x_3549_, 3, v___y_3514_);
lean_ctor_set(v___x_3549_, 4, v___y_3534_);
lean_ctor_set(v___x_3549_, 5, v___y_3515_);
lean_ctor_set(v___x_3549_, 6, v___y_3545_);
lean_ctor_set(v___x_3549_, 7, v___y_3527_);
lean_ctor_set(v___x_3549_, 8, v___y_3532_);
lean_ctor_set(v___x_3549_, 9, v___y_3542_);
lean_ctor_set(v___x_3549_, 10, v___y_3540_);
lean_ctor_set(v___x_3549_, 11, v___y_3522_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12, v___y_3526_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12 + 1, v___y_3528_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12 + 2, v___y_3524_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12 + 3, v___y_3529_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12 + 4, v___y_3548_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*12 + 5, v___y_3521_);
lean_inc_ref(v___y_3544_);
v___x_3550_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3544_, v___x_3549_, v___y_3539_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3550_, 1);
lean_inc_ref(v___y_3517_);
v___x_3551_ = l_Lean_Meta_Grind_propagateBeta(v___y_3517_, v___y_3525_, v___y_3539_, v___y_3536_, v___y_3541_, v___y_3538_, v___y_3523_, v___y_3537_, v___y_3543_, v___y_3546_, v___y_3518_, v___y_3547_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
lean_inc_ref(v___y_3531_);
v___x_3552_ = l_Lean_Meta_Grind_propagateBeta(v___y_3531_, v___y_3530_, v___y_3539_, v___y_3536_, v___y_3541_, v___y_3538_, v___y_3523_, v___y_3537_, v___y_3543_, v___y_3546_, v___y_3518_, v___y_3547_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v___x_3553_; 
lean_dec_ref_known(v___x_3552_, 1);
v___x_3553_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3447_, v_lhsRoot_3446_, v___y_3539_, v___y_3543_, v___y_3546_, v___y_3518_, v___y_3547_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3533_, v___y_3539_);
lean_dec_ref(v___y_3533_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v___x_3556_; 
lean_dec_ref_known(v___x_3555_, 1);
lean_inc_ref(v___y_3544_);
v___x_3556_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3513_, v___y_3544_, v___y_3539_, v___y_3536_, v___y_3541_, v___y_3538_, v___y_3523_, v___y_3537_, v___y_3543_, v___y_3546_, v___y_3518_, v___y_3547_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref_known(v___x_3556_, 1);
v___x_3557_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3539_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; uint8_t v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = lean_unbox(v_a_3558_);
lean_dec(v_a_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; 
v___x_3560_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3520_, v___y_3539_, v___y_3536_, v___y_3541_, v___y_3538_, v___y_3523_, v___y_3537_, v___y_3543_, v___y_3546_, v___y_3518_, v___y_3547_);
lean_dec_ref(v___y_3520_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_dec_ref_known(v___x_3560_, 1);
v___y_3461_ = v___y_3513_;
v___y_3462_ = v_a_3554_;
v___y_3463_ = v___y_3516_;
v___y_3464_ = v___y_3517_;
v___y_3465_ = v___y_3544_;
v___y_3466_ = v___y_3531_;
v___y_3467_ = v___y_3539_;
v___y_3468_ = v___y_3536_;
v___y_3469_ = v___y_3541_;
v___y_3470_ = v___y_3538_;
v___y_3471_ = v___y_3523_;
v___y_3472_ = v___y_3537_;
v___y_3473_ = v___y_3543_;
v___y_3474_ = v___y_3546_;
v___y_3475_ = v___y_3518_;
v___y_3476_ = v___y_3547_;
goto v___jp_3460_;
}
else
{
lean_dec(v_a_3554_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
return v___x_3560_;
}
}
else
{
lean_dec_ref(v___y_3520_);
v___y_3461_ = v___y_3513_;
v___y_3462_ = v_a_3554_;
v___y_3463_ = v___y_3516_;
v___y_3464_ = v___y_3517_;
v___y_3465_ = v___y_3544_;
v___y_3466_ = v___y_3531_;
v___y_3467_ = v___y_3539_;
v___y_3468_ = v___y_3536_;
v___y_3469_ = v___y_3541_;
v___y_3470_ = v___y_3538_;
v___y_3471_ = v___y_3523_;
v___y_3472_ = v___y_3537_;
v___y_3473_ = v___y_3543_;
v___y_3474_ = v___y_3546_;
v___y_3475_ = v___y_3518_;
v___y_3476_ = v___y_3547_;
goto v___jp_3460_;
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_a_3554_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
v_a_3561_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3557_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3557_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_dec(v_a_3554_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
return v___x_3556_;
}
}
else
{
lean_dec(v_a_3554_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
return v___x_3555_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
v_a_3569_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3553_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3553_);
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
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
return v___x_3552_;
}
}
else
{
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
return v___x_3551_;
}
}
else
{
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3513_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
return v___x_3550_;
}
}
v___jp_3577_:
{
if (v_isHEq_3441_ == 0)
{
if (v___y_3589_ == 0)
{
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3582_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3584_;
v___y_3521_ = v___y_3583_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3591_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3614_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3604_;
v___y_3538_ = v___y_3603_;
v___y_3539_ = v___y_3605_;
v___y_3540_ = v___y_3607_;
v___y_3541_ = v___y_3606_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v___y_3610_;
v___y_3545_ = v___y_3611_;
v___y_3546_ = v___y_3612_;
v___y_3547_ = v___y_3613_;
v___y_3548_ = v___y_3587_;
goto v___jp_3512_;
}
else
{
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3582_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3584_;
v___y_3521_ = v___y_3583_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3591_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3614_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3604_;
v___y_3538_ = v___y_3603_;
v___y_3539_ = v___y_3605_;
v___y_3540_ = v___y_3607_;
v___y_3541_ = v___y_3606_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v___y_3610_;
v___y_3545_ = v___y_3611_;
v___y_3546_ = v___y_3612_;
v___y_3547_ = v___y_3613_;
v___y_3548_ = v___y_3589_;
goto v___jp_3512_;
}
}
else
{
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3578_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3582_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3584_;
v___y_3521_ = v___y_3583_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3591_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3593_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3614_;
v___y_3530_ = v___y_3596_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v___y_3602_;
v___y_3537_ = v___y_3604_;
v___y_3538_ = v___y_3603_;
v___y_3539_ = v___y_3605_;
v___y_3540_ = v___y_3607_;
v___y_3541_ = v___y_3606_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3609_;
v___y_3544_ = v___y_3610_;
v___y_3545_ = v___y_3611_;
v___y_3546_ = v___y_3612_;
v___y_3547_ = v___y_3613_;
v___y_3548_ = v_isHEq_3441_;
goto v___jp_3512_;
}
}
v___jp_3615_:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3617_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
lean_dec_ref_known(v___x_3638_, 1);
v___x_3639_ = 0;
v___x_3640_ = lean_st_ref_get(v___y_3628_);
v___x_3641_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3640_, v_lhs_3442_, v___x_3639_);
lean_dec(v___x_3640_);
v___x_3642_ = lean_st_ref_get(v___y_3628_);
lean_inc_ref(v___y_3616_);
v___x_3643_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3642_, v___y_3616_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___x_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v_self_3645_; lean_object* v_root_3646_; lean_object* v_congr_3647_; lean_object* v_target_x3f_3648_; lean_object* v_proof_x3f_3649_; uint8_t v_flipped_3650_; lean_object* v_size_3651_; uint8_t v_interpreted_3652_; uint8_t v_ctor_3653_; uint8_t v_hasLambdas_3654_; uint8_t v_heqProofs_3655_; lean_object* v_idx_3656_; lean_object* v_generation_3657_; lean_object* v_mt_3658_; lean_object* v_sTerms_3659_; uint8_t v_funCC_3660_; lean_object* v_ematchDiagSource_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3688_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v_self_3645_ = lean_ctor_get(v_a_3644_, 0);
v_root_3646_ = lean_ctor_get(v_a_3644_, 2);
v_congr_3647_ = lean_ctor_get(v_a_3644_, 3);
v_target_x3f_3648_ = lean_ctor_get(v_a_3644_, 4);
v_proof_x3f_3649_ = lean_ctor_get(v_a_3644_, 5);
v_flipped_3650_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12);
v_size_3651_ = lean_ctor_get(v_a_3644_, 6);
v_interpreted_3652_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12 + 1);
v_ctor_3653_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12 + 2);
v_hasLambdas_3654_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12 + 3);
v_heqProofs_3655_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12 + 4);
v_idx_3656_ = lean_ctor_get(v_a_3644_, 7);
v_generation_3657_ = lean_ctor_get(v_a_3644_, 8);
v_mt_3658_ = lean_ctor_get(v_a_3644_, 9);
v_sTerms_3659_ = lean_ctor_get(v_a_3644_, 10);
v_funCC_3660_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3661_ = lean_ctor_get(v_a_3644_, 11);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_a_3644_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v_a_3644_, 1);
lean_dec(v_unused_3689_);
v___x_3663_ = v_a_3644_;
v_isShared_3664_ = v_isSharedCheck_3688_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_ematchDiagSource_3661_);
lean_inc(v_sTerms_3659_);
lean_inc(v_mt_3658_);
lean_inc(v_generation_3657_);
lean_inc(v_idx_3656_);
lean_inc(v_size_3651_);
lean_inc(v_proof_x3f_3649_);
lean_inc(v_target_x3f_3648_);
lean_inc(v_congr_3647_);
lean_inc(v_root_3646_);
lean_inc(v_self_3645_);
lean_dec(v_a_3644_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3688_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v_self_3665_; lean_object* v_next_3666_; lean_object* v_root_3667_; lean_object* v_congr_3668_; lean_object* v_target_x3f_3669_; lean_object* v_proof_x3f_3670_; uint8_t v_flipped_3671_; lean_object* v_size_3672_; uint8_t v_interpreted_3673_; uint8_t v_ctor_3674_; uint8_t v_hasLambdas_3675_; uint8_t v_heqProofs_3676_; lean_object* v_idx_3677_; lean_object* v_generation_3678_; lean_object* v_mt_3679_; lean_object* v_sTerms_3680_; uint8_t v_funCC_3681_; lean_object* v_ematchDiagSource_3682_; lean_object* v___x_3684_; 
v_self_3665_ = lean_ctor_get(v_rhsRoot_3447_, 0);
v_next_3666_ = lean_ctor_get(v_rhsRoot_3447_, 1);
v_root_3667_ = lean_ctor_get(v_rhsRoot_3447_, 2);
v_congr_3668_ = lean_ctor_get(v_rhsRoot_3447_, 3);
v_target_x3f_3669_ = lean_ctor_get(v_rhsRoot_3447_, 4);
v_proof_x3f_3670_ = lean_ctor_get(v_rhsRoot_3447_, 5);
v_flipped_3671_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12);
v_size_3672_ = lean_ctor_get(v_rhsRoot_3447_, 6);
v_interpreted_3673_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12 + 1);
v_ctor_3674_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12 + 2);
v_hasLambdas_3675_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12 + 3);
v_heqProofs_3676_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12 + 4);
v_idx_3677_ = lean_ctor_get(v_rhsRoot_3447_, 7);
v_generation_3678_ = lean_ctor_get(v_rhsRoot_3447_, 8);
v_mt_3679_ = lean_ctor_get(v_rhsRoot_3447_, 9);
v_sTerms_3680_ = lean_ctor_get(v_rhsRoot_3447_, 10);
v_funCC_3681_ = lean_ctor_get_uint8(v_rhsRoot_3447_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3682_ = lean_ctor_get(v_rhsRoot_3447_, 11);
lean_inc_ref(v_next_3666_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v_next_3666_);
v___x_3684_ = v___x_3663_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_self_3645_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_next_3666_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_root_3646_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_congr_3647_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_target_x3f_3648_);
lean_ctor_set(v_reuseFailAlloc_3687_, 5, v_proof_x3f_3649_);
lean_ctor_set(v_reuseFailAlloc_3687_, 6, v_size_3651_);
lean_ctor_set(v_reuseFailAlloc_3687_, 7, v_idx_3656_);
lean_ctor_set(v_reuseFailAlloc_3687_, 8, v_generation_3657_);
lean_ctor_set(v_reuseFailAlloc_3687_, 9, v_mt_3658_);
lean_ctor_set(v_reuseFailAlloc_3687_, 10, v_sTerms_3659_);
lean_ctor_set(v_reuseFailAlloc_3687_, 11, v_ematchDiagSource_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12, v_flipped_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12 + 1, v_interpreted_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12 + 2, v_ctor_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12 + 3, v_hasLambdas_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12 + 4, v_heqProofs_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*12 + 5, v_funCC_3660_);
v___x_3684_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3619_, v___x_3684_, v___y_3628_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3686_; 
lean_dec_ref_known(v___x_3685_, 1);
v___x_3686_ = lean_nat_add(v_size_3672_, v___y_3622_);
lean_dec(v___y_3622_);
if (v_hasLambdas_3675_ == 0)
{
lean_inc(v_mt_3679_);
lean_inc(v_sTerms_3680_);
lean_inc_ref(v_root_3667_);
lean_inc(v_target_x3f_3669_);
lean_inc(v_generation_3678_);
lean_inc(v_idx_3677_);
lean_inc(v_ematchDiagSource_3682_);
lean_inc_ref(v_self_3665_);
lean_inc(v_proof_x3f_3670_);
lean_inc_ref(v_congr_3668_);
v___y_3578_ = v_congr_3668_;
v___y_3579_ = v___y_3617_;
v___y_3580_ = v_proof_x3f_3670_;
v___y_3581_ = v___x_3641_;
v___y_3582_ = v___y_3618_;
v___y_3583_ = v_funCC_3681_;
v___y_3584_ = v_self_3665_;
v___y_3585_ = v___y_3626_;
v___y_3586_ = v___y_3636_;
v___y_3587_ = v___y_3627_;
v___y_3588_ = v_ematchDiagSource_3682_;
v___y_3589_ = v_heqProofs_3676_;
v___y_3590_ = v_ctor_3674_;
v___y_3591_ = v___y_3632_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v_flipped_3671_;
v___y_3594_ = v_idx_3677_;
v___y_3595_ = v_interpreted_3673_;
v___y_3596_ = v___y_3620_;
v___y_3597_ = v___y_3624_;
v___y_3598_ = v_generation_3678_;
v___y_3599_ = v___y_3616_;
v___y_3600_ = v_target_x3f_3669_;
v___y_3601_ = v_root_3667_;
v___y_3602_ = v___y_3629_;
v___y_3603_ = v___y_3631_;
v___y_3604_ = v___y_3633_;
v___y_3605_ = v___y_3628_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v_sTerms_3680_;
v___y_3608_ = v_mt_3679_;
v___y_3609_ = v___y_3634_;
v___y_3610_ = v___y_3621_;
v___y_3611_ = v___x_3686_;
v___y_3612_ = v___y_3635_;
v___y_3613_ = v___y_3637_;
v___y_3614_ = v___y_3623_;
goto v___jp_3577_;
}
else
{
lean_inc(v_mt_3679_);
lean_inc(v_sTerms_3680_);
lean_inc_ref(v_root_3667_);
lean_inc(v_target_x3f_3669_);
lean_inc(v_generation_3678_);
lean_inc(v_idx_3677_);
lean_inc(v_ematchDiagSource_3682_);
lean_inc_ref(v_self_3665_);
lean_inc(v_proof_x3f_3670_);
lean_inc_ref(v_congr_3668_);
v___y_3578_ = v_congr_3668_;
v___y_3579_ = v___y_3617_;
v___y_3580_ = v_proof_x3f_3670_;
v___y_3581_ = v___x_3641_;
v___y_3582_ = v___y_3618_;
v___y_3583_ = v_funCC_3681_;
v___y_3584_ = v_self_3665_;
v___y_3585_ = v___y_3626_;
v___y_3586_ = v___y_3636_;
v___y_3587_ = v___y_3627_;
v___y_3588_ = v_ematchDiagSource_3682_;
v___y_3589_ = v_heqProofs_3676_;
v___y_3590_ = v_ctor_3674_;
v___y_3591_ = v___y_3632_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v_flipped_3671_;
v___y_3594_ = v_idx_3677_;
v___y_3595_ = v_interpreted_3673_;
v___y_3596_ = v___y_3620_;
v___y_3597_ = v___y_3624_;
v___y_3598_ = v_generation_3678_;
v___y_3599_ = v___y_3616_;
v___y_3600_ = v_target_x3f_3669_;
v___y_3601_ = v_root_3667_;
v___y_3602_ = v___y_3629_;
v___y_3603_ = v___y_3631_;
v___y_3604_ = v___y_3633_;
v___y_3605_ = v___y_3628_;
v___y_3606_ = v___y_3630_;
v___y_3607_ = v_sTerms_3680_;
v___y_3608_ = v_mt_3679_;
v___y_3609_ = v___y_3634_;
v___y_3610_ = v___y_3621_;
v___y_3611_ = v___x_3686_;
v___y_3612_ = v___y_3635_;
v___y_3613_ = v___y_3637_;
v___y_3614_ = v_hasLambdas_3675_;
goto v___jp_3577_;
}
}
else
{
lean_dec(v___x_3641_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___x_3641_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
v_a_3690_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3643_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3643_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_dec_ref(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
return v___x_3638_;
}
}
v___jp_3703_:
{
lean_object* v_self_3719_; lean_object* v_next_3720_; lean_object* v_size_3721_; uint8_t v_hasLambdas_3722_; uint8_t v_heqProofs_3723_; lean_object* v___x_3724_; 
v_self_3719_ = lean_ctor_get(v_lhsRoot_3446_, 0);
v_next_3720_ = lean_ctor_get(v_lhsRoot_3446_, 1);
v_size_3721_ = lean_ctor_get(v_lhsRoot_3446_, 6);
v_hasLambdas_3722_ = lean_ctor_get_uint8(v_lhsRoot_3446_, sizeof(void*)*12 + 3);
v_heqProofs_3723_ = lean_ctor_get_uint8(v_lhsRoot_3446_, sizeof(void*)*12 + 4);
v___x_3724_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3719_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v_root_3726_; lean_object* v___x_3727_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v_root_3726_ = lean_ctor_get(v_rhsNode_3445_, 2);
lean_inc_ref_n(v_root_3726_, 2);
lean_dec_ref(v_rhsNode_3445_);
lean_inc_ref(v_lhs_3442_);
v___x_3727_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3442_, v_root_3726_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_toCold_3728_; lean_object* v_options_3729_; uint8_t v_hasTrace_3730_; 
lean_dec_ref_known(v___x_3727_, 1);
v_toCold_3728_ = lean_ctor_get(v___y_3717_, 0);
v_options_3729_ = lean_ctor_get(v_toCold_3728_, 2);
v_hasTrace_3730_ = lean_ctor_get_uint8(v_options_3729_, sizeof(void*)*1);
if (v_hasTrace_3730_ == 0)
{
lean_inc_ref(v_next_3720_);
lean_inc(v_size_3721_);
lean_inc_ref(v_self_3719_);
v___y_3616_ = v_self_3719_;
v___y_3617_ = v_a_3725_;
v___y_3618_ = v___y_3705_;
v___y_3619_ = v___y_3704_;
v___y_3620_ = v_fns_u2082_3708_;
v___y_3621_ = v_root_3726_;
v___y_3622_ = v_size_3721_;
v___y_3623_ = v_hasLambdas_3722_;
v___y_3624_ = v___y_3707_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v_next_3720_;
v___y_3627_ = v_heqProofs_3723_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
v___y_3634_ = v___y_3715_;
v___y_3635_ = v___y_3716_;
v___y_3636_ = v___y_3717_;
v___y_3637_ = v___y_3718_;
goto v___jp_3615_;
}
else
{
lean_object* v_inheritedTraceOptions_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_inheritedTraceOptions_3731_ = lean_ctor_get(v_toCold_3728_, 11);
v___x_3732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3731_, v_options_3729_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_inc_ref(v_next_3720_);
lean_inc(v_size_3721_);
lean_inc_ref(v_self_3719_);
v___y_3616_ = v_self_3719_;
v___y_3617_ = v_a_3725_;
v___y_3618_ = v___y_3705_;
v___y_3619_ = v___y_3704_;
v___y_3620_ = v_fns_u2082_3708_;
v___y_3621_ = v_root_3726_;
v___y_3622_ = v_size_3721_;
v___y_3623_ = v_hasLambdas_3722_;
v___y_3624_ = v___y_3707_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v_next_3720_;
v___y_3627_ = v_heqProofs_3723_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
v___y_3634_ = v___y_3715_;
v___y_3635_ = v___y_3716_;
v___y_3636_ = v___y_3717_;
v___y_3637_ = v___y_3718_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Meta_Grind_updateLastTag(v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; 
lean_dec_ref_known(v___x_3734_, 1);
lean_inc_ref(v_lhs_3442_);
v___x_3735_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3442_, v___y_3709_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
lean_inc_ref(v_root_3726_);
v___x_3737_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3726_, v___y_3709_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = lean_st_ref_get(v___y_3709_);
lean_inc_ref(v_lhs_3442_);
v___x_3740_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3739_, v_lhs_3442_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___x_3739_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3741_, v___y_3709_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v_a_3736_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v_a_3738_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v_a_3743_);
v___x_3750_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3702_, v___x_3749_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_dec_ref_known(v___x_3750_, 1);
lean_inc_ref(v_next_3720_);
lean_inc(v_size_3721_);
lean_inc_ref(v_self_3719_);
v___y_3616_ = v_self_3719_;
v___y_3617_ = v_a_3725_;
v___y_3618_ = v___y_3705_;
v___y_3619_ = v___y_3704_;
v___y_3620_ = v_fns_u2082_3708_;
v___y_3621_ = v_root_3726_;
v___y_3622_ = v_size_3721_;
v___y_3623_ = v_hasLambdas_3722_;
v___y_3624_ = v___y_3707_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v_next_3720_;
v___y_3627_ = v_heqProofs_3723_;
v___y_3628_ = v___y_3709_;
v___y_3629_ = v___y_3710_;
v___y_3630_ = v___y_3711_;
v___y_3631_ = v___y_3712_;
v___y_3632_ = v___y_3713_;
v___y_3633_ = v___y_3714_;
v___y_3634_ = v___y_3715_;
v___y_3635_ = v___y_3716_;
v___y_3636_ = v___y_3717_;
v___y_3637_ = v___y_3718_;
goto v___jp_3615_;
}
else
{
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
return v___x_3750_;
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v_a_3738_);
lean_dec(v_a_3736_);
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
v_a_3751_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3742_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3742_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v_a_3738_);
lean_dec(v_a_3736_);
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
v_a_3759_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3740_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3740_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3736_);
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
v_a_3767_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3737_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3737_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
v_a_3775_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3735_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3735_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
return v___x_3734_;
}
}
}
}
else
{
lean_dec_ref(v_root_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_lhs_3442_);
return v___x_3727_;
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_fns_u2082_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
v_a_3783_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3724_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3724_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
v___jp_3791_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3806_ = lean_array_get_size(v___y_3794_);
v___x_3807_ = lean_unsigned_to_nat(0u);
v___x_3808_ = lean_nat_dec_eq(v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_object* v_self_3809_; lean_object* v___x_3810_; 
v_self_3809_ = lean_ctor_get(v_lhsRoot_3446_, 0);
lean_inc_ref(v_self_3809_);
v___x_3810_ = l_Lean_Meta_Grind_getFnRoots(v_self_3809_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v___x_3810_, 1);
v___y_3704_ = v___y_3793_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v_fns_u2081_3795_;
v___y_3707_ = v___y_3794_;
v_fns_u2082_3708_ = v_a_3811_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
goto v___jp_3703_;
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_fns_u2081_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
v_a_3812_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3810_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3810_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v___x_3820_; 
v___x_3820_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3704_ = v___y_3793_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v_fns_u2081_3795_;
v___y_3707_ = v___y_3794_;
v_fns_u2082_3708_ = v___x_3820_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
goto v___jp_3703_;
}
}
v___jp_3821_:
{
lean_object* v___x_3832_; 
lean_inc_ref(v_lhs_3442_);
v___x_3832_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3442_, v___y_3822_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3900_; 
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; 
v_unused_3901_ = lean_ctor_get(v___x_3832_, 0);
lean_dec(v_unused_3901_);
v___x_3834_ = v___x_3832_;
v_isShared_3835_ = v_isSharedCheck_3900_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v___x_3832_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3900_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v_self_3836_; lean_object* v_next_3837_; lean_object* v_root_3838_; lean_object* v_congr_3839_; lean_object* v_size_3840_; uint8_t v_interpreted_3841_; uint8_t v_ctor_3842_; uint8_t v_hasLambdas_3843_; uint8_t v_heqProofs_3844_; lean_object* v_idx_3845_; lean_object* v_generation_3846_; lean_object* v_mt_3847_; lean_object* v_sTerms_3848_; uint8_t v_funCC_3849_; lean_object* v_ematchDiagSource_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3897_; 
v_self_3836_ = lean_ctor_get(v_lhsNode_3444_, 0);
v_next_3837_ = lean_ctor_get(v_lhsNode_3444_, 1);
v_root_3838_ = lean_ctor_get(v_lhsNode_3444_, 2);
v_congr_3839_ = lean_ctor_get(v_lhsNode_3444_, 3);
v_size_3840_ = lean_ctor_get(v_lhsNode_3444_, 6);
v_interpreted_3841_ = lean_ctor_get_uint8(v_lhsNode_3444_, sizeof(void*)*12 + 1);
v_ctor_3842_ = lean_ctor_get_uint8(v_lhsNode_3444_, sizeof(void*)*12 + 2);
v_hasLambdas_3843_ = lean_ctor_get_uint8(v_lhsNode_3444_, sizeof(void*)*12 + 3);
v_heqProofs_3844_ = lean_ctor_get_uint8(v_lhsNode_3444_, sizeof(void*)*12 + 4);
v_idx_3845_ = lean_ctor_get(v_lhsNode_3444_, 7);
v_generation_3846_ = lean_ctor_get(v_lhsNode_3444_, 8);
v_mt_3847_ = lean_ctor_get(v_lhsNode_3444_, 9);
v_sTerms_3848_ = lean_ctor_get(v_lhsNode_3444_, 10);
v_funCC_3849_ = lean_ctor_get_uint8(v_lhsNode_3444_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3850_ = lean_ctor_get(v_lhsNode_3444_, 11);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_lhsNode_3444_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3898_ = lean_ctor_get(v_lhsNode_3444_, 5);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_lhsNode_3444_, 4);
lean_dec(v_unused_3899_);
v___x_3852_ = v_lhsNode_3444_;
v_isShared_3853_ = v_isSharedCheck_3897_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_ematchDiagSource_3850_);
lean_inc(v_sTerms_3848_);
lean_inc(v_mt_3847_);
lean_inc(v_generation_3846_);
lean_inc(v_idx_3845_);
lean_inc(v_size_3840_);
lean_inc(v_congr_3839_);
lean_inc(v_root_3838_);
lean_inc(v_next_3837_);
lean_inc(v_self_3836_);
lean_dec(v_lhsNode_3444_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3897_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3835_ == 0)
{
lean_ctor_set_tag(v___x_3834_, 1);
lean_ctor_set(v___x_3834_, 0, v_rhs_3443_);
v___x_3855_ = v___x_3834_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_rhs_3443_);
v___x_3855_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_proof_3440_);
lean_inc_ref(v_root_3838_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 5, v___x_3856_);
lean_ctor_set(v___x_3852_, 4, v___x_3855_);
v___x_3858_ = v___x_3852_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_self_3836_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_next_3837_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_root_3838_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v_congr_3839_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3895_, 5, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3895_, 6, v_size_3840_);
lean_ctor_set(v_reuseFailAlloc_3895_, 7, v_idx_3845_);
lean_ctor_set(v_reuseFailAlloc_3895_, 8, v_generation_3846_);
lean_ctor_set(v_reuseFailAlloc_3895_, 9, v_mt_3847_);
lean_ctor_set(v_reuseFailAlloc_3895_, 10, v_sTerms_3848_);
lean_ctor_set(v_reuseFailAlloc_3895_, 11, v_ematchDiagSource_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*12 + 1, v_interpreted_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*12 + 2, v_ctor_3842_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*12 + 3, v_hasLambdas_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*12 + 4, v_heqProofs_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3895_, sizeof(void*)*12 + 5, v_funCC_3849_);
v___x_3858_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; 
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*12, v_flipped_3448_);
lean_inc_ref(v_lhs_3442_);
v___x_3859_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3442_, v___x_3858_, v___y_3822_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; 
lean_dec_ref_known(v___x_3859_, 1);
v___x_3860_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3446_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3447_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___x_3864_ = lean_array_get_size(v_a_3861_);
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = lean_nat_dec_eq(v___x_3864_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v_self_3867_; lean_object* v___x_3868_; 
v_self_3867_ = lean_ctor_get(v_rhsRoot_3447_, 0);
lean_inc_ref(v_self_3867_);
v___x_3868_ = l_Lean_Meta_Grind_getFnRoots(v_self_3867_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___y_3792_ = v_a_3861_;
v___y_3793_ = v_root_3838_;
v___y_3794_ = v_a_3863_;
v_fns_u2081_3795_ = v_a_3869_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
goto v___jp_3791_;
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3863_);
lean_dec(v_a_3861_);
lean_dec_ref(v_root_3838_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
v_a_3870_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3868_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3868_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v___x_3878_; 
v___x_3878_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3792_ = v_a_3861_;
v___y_3793_ = v_root_3838_;
v___y_3794_ = v_a_3863_;
v_fns_u2081_3795_ = v___x_3878_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
goto v___jp_3791_;
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_a_3861_);
lean_dec_ref(v_root_3838_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
v_a_3879_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3862_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3862_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_root_3838_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
v_a_3887_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3860_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3860_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_dec_ref(v_root_3838_);
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhs_3442_);
return v___x_3859_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3447_);
lean_dec_ref(v_lhsRoot_3446_);
lean_dec_ref(v_rhsNode_3445_);
lean_dec_ref(v_lhsNode_3444_);
lean_dec_ref(v_rhs_3443_);
lean_dec_ref(v_lhs_3442_);
lean_dec_ref(v_proof_3440_);
return v___x_3832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3931_ = _args[0];
lean_object* v_isHEq_3932_ = _args[1];
lean_object* v_lhs_3933_ = _args[2];
lean_object* v_rhs_3934_ = _args[3];
lean_object* v_lhsNode_3935_ = _args[4];
lean_object* v_rhsNode_3936_ = _args[5];
lean_object* v_lhsRoot_3937_ = _args[6];
lean_object* v_rhsRoot_3938_ = _args[7];
lean_object* v_flipped_3939_ = _args[8];
lean_object* v_a_3940_ = _args[9];
lean_object* v_a_3941_ = _args[10];
lean_object* v_a_3942_ = _args[11];
lean_object* v_a_3943_ = _args[12];
lean_object* v_a_3944_ = _args[13];
lean_object* v_a_3945_ = _args[14];
lean_object* v_a_3946_ = _args[15];
lean_object* v_a_3947_ = _args[16];
lean_object* v_a_3948_ = _args[17];
lean_object* v_a_3949_ = _args[18];
lean_object* v_a_3950_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3951_; uint8_t v_flipped_boxed_3952_; lean_object* v_res_3953_; 
v_isHEq_boxed_3951_ = lean_unbox(v_isHEq_3932_);
v_flipped_boxed_3952_ = lean_unbox(v_flipped_3939_);
v_res_3953_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3931_, v_isHEq_boxed_3951_, v_lhs_3933_, v_rhs_3934_, v_lhsNode_3935_, v_rhsNode_3936_, v_lhsRoot_3937_, v_rhsRoot_3938_, v_flipped_boxed_3952_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec(v_a_3940_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3954_, lean_object* v_as_x27_3955_, lean_object* v_b_3956_, lean_object* v_a_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; 
v___x_3969_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3955_, v_b_3956_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3970_, lean_object* v_as_x27_3971_, lean_object* v_b_3972_, lean_object* v_a_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3970_, v_as_x27_3971_, v_b_3972_, v_a_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec(v_as_x27_3971_);
lean_dec(v_as_3970_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3986_, lean_object* v_as_x27_3987_, lean_object* v_b_3988_, lean_object* v_a_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3987_, v_b_3988_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4002_, lean_object* v_as_x27_4003_, lean_object* v_b_4004_, lean_object* v_a_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4002_, v_as_x27_4003_, v_b_4004_, v_a_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec(v_as_x27_4003_);
lean_dec(v_as_4002_);
return v_res_4017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4020_ = l_Lean_stringToMessageData(v___x_4019_);
return v___x_4020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4026_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4027_ = l_Lean_Name_append(v___x_4026_, v___x_4025_);
return v___x_4027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
return v___x_4030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4034_, lean_object* v_rhs_4035_, lean_object* v_proof_4036_, uint8_t v_isHEq_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_st_ref_get(v_a_4038_);
lean_inc_ref(v_lhs_4034_);
v___x_4053_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4052_, v_lhs_4034_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v___x_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4055_ = lean_st_ref_get(v_a_4038_);
lean_inc_ref(v_rhs_4035_);
v___x_4056_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4055_, v_rhs_4035_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v___x_4055_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v_root_4058_; lean_object* v_root_4059_; size_t v___x_4060_; size_t v___x_4061_; uint8_t v___x_4062_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v_root_4058_ = lean_ctor_get(v_a_4054_, 2);
v_root_4059_ = lean_ctor_get(v_a_4057_, 2);
v___x_4060_ = lean_ptr_addr(v_root_4058_);
v___x_4061_ = lean_ptr_addr(v_root_4059_);
v___x_4062_ = lean_usize_dec_eq(v___x_4060_, v___x_4061_);
if (v___x_4062_ == 0)
{
lean_object* v_toCold_4063_; lean_object* v_options_4064_; lean_object* v_inheritedTraceOptions_4065_; uint8_t v_hasTrace_4066_; uint8_t v___x_4067_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4133_; uint8_t v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4163_; lean_object* v___y_4164_; uint8_t v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; uint8_t v___y_4182_; lean_object* v___y_4183_; uint8_t v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; uint8_t v___y_4198_; lean_object* v___y_4199_; uint8_t v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___y_4214_; lean_object* v___y_4215_; uint8_t v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v_size_4224_; uint8_t v_interpreted_4225_; uint8_t v_ctor_4226_; lean_object* v___y_4227_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; uint8_t v___y_4234_; lean_object* v___y_4235_; uint8_t v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; uint8_t v_ctor_4245_; lean_object* v___y_4253_; lean_object* v___y_4254_; uint8_t v_valueInconsistency_4255_; uint8_t v_trueEqFalse_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; 
v_toCold_4063_ = lean_ctor_get(v_a_4046_, 0);
v_options_4064_ = lean_ctor_get(v_toCold_4063_, 2);
v_inheritedTraceOptions_4065_ = lean_ctor_get(v_toCold_4063_, 11);
v_hasTrace_4066_ = lean_ctor_get_uint8(v_options_4064_, sizeof(void*)*1);
v___x_4067_ = 1;
if (v_hasTrace_4066_ == 0)
{
v___y_4312_ = v_a_4038_;
v___y_4313_ = v_a_4039_;
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
goto v___jp_4311_;
}
else
{
lean_object* v___x_4355_; lean_object* v_____do__lift_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___x_4370_; uint8_t v___x_4371_; 
v___x_4355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4065_, v_options_4064_, v___x_4370_);
if (v___x_4371_ == 0)
{
v___y_4312_ = v_a_4038_;
v___y_4313_ = v_a_4039_;
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
goto v___jp_4311_;
}
else
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_Meta_Grind_updateLastTag(v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_dec_ref_known(v___x_4372_, 1);
if (v_isHEq_4037_ == 0)
{
lean_object* v___x_4373_; 
lean_inc_ref(v_rhs_4035_);
lean_inc_ref(v_lhs_4034_);
v___x_4373_ = l_Lean_Meta_mkEq(v_lhs_4034_, v_rhs_4035_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___x_4373_, 1);
v_____do__lift_4357_ = v_a_4374_;
v___y_4358_ = v_a_4038_;
v___y_4359_ = v_a_4039_;
v___y_4360_ = v_a_4040_;
v___y_4361_ = v_a_4041_;
v___y_4362_ = v_a_4042_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
goto v___jp_4356_;
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4375_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4373_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4373_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
else
{
lean_object* v___x_4383_; 
lean_inc_ref(v_rhs_4035_);
lean_inc_ref(v_lhs_4034_);
v___x_4383_ = l_Lean_Meta_mkHEq(v_lhs_4034_, v_rhs_4035_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4383_, 1);
v_____do__lift_4357_ = v_a_4384_;
v___y_4358_ = v_a_4038_;
v___y_4359_ = v_a_4039_;
v___y_4360_ = v_a_4040_;
v___y_4361_ = v_a_4041_;
v___y_4362_ = v_a_4042_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
goto v___jp_4356_;
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4385_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4383_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4383_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
else
{
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
return v___x_4372_;
}
}
v___jp_4356_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = l_Lean_MessageData_ofExpr(v_____do__lift_4357_);
v___x_4369_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4355_, v___x_4368_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_dec_ref_known(v___x_4369_, 1);
v___y_4312_ = v___y_4358_;
v___y_4313_ = v___y_4359_;
v___y_4314_ = v___y_4360_;
v___y_4315_ = v___y_4361_;
v___y_4316_ = v___y_4362_;
v___y_4317_ = v___y_4363_;
v___y_4318_ = v___y_4364_;
v___y_4319_ = v___y_4365_;
v___y_4320_ = v___y_4366_;
v___y_4321_ = v___y_4367_;
goto v___jp_4311_;
}
else
{
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
return v___x_4369_;
}
}
}
v___jp_4068_:
{
lean_object* v_toCold_4079_; lean_object* v_options_4080_; uint8_t v_hasTrace_4081_; 
v_toCold_4079_ = lean_ctor_get(v___y_4077_, 0);
v_options_4080_ = lean_ctor_get(v_toCold_4079_, 2);
v_hasTrace_4081_ = lean_ctor_get_uint8(v_options_4080_, sizeof(void*)*1);
if (v_hasTrace_4081_ == 0)
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Meta_Grind_checkInvariants(v___x_4062_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4082_;
}
else
{
lean_object* v_inheritedTraceOptions_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_inheritedTraceOptions_4083_ = lean_ctor_get(v_toCold_4079_, 11);
v___x_4084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4086_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4083_, v_options_4080_, v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_Meta_Grind_checkInvariants(v___x_4062_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4087_;
}
else
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Meta_Grind_updateLastTag(v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref_known(v___x_4088_, 1);
v___x_4089_ = lean_st_ref_get(v___y_4069_);
v___x_4090_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4089_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___x_4089_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
lean_ctor_set(v___x_4093_, 1, v_a_4091_);
v___x_4094_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4084_, v___x_4093_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v___x_4095_; 
lean_dec_ref_known(v___x_4094_, 1);
v___x_4095_ = l_Lean_Meta_Grind_checkInvariants(v___x_4062_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4095_;
}
else
{
return v___x_4094_;
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
v_a_4096_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4090_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4090_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
return v___x_4088_;
}
}
}
}
v___jp_4104_:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4108_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; uint8_t v___x_4120_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4120_ = lean_unbox(v_a_4119_);
lean_dec(v_a_4119_);
if (v___x_4120_ == 0)
{
if (v___y_4106_ == 0)
{
lean_dec_ref(v___y_4107_);
lean_dec_ref(v___y_4105_);
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
goto v___jp_4068_;
}
else
{
lean_object* v_self_4121_; lean_object* v_self_4122_; lean_object* v___x_4123_; 
v_self_4121_ = lean_ctor_get(v___y_4107_, 0);
lean_inc_ref(v_self_4121_);
lean_dec_ref(v___y_4107_);
v_self_4122_ = lean_ctor_get(v___y_4105_, 0);
lean_inc_ref(v_self_4122_);
lean_dec_ref(v___y_4105_);
v___x_4123_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4121_, v_self_4122_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_dec_ref_known(v___x_4123_, 1);
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
goto v___jp_4068_;
}
else
{
return v___x_4123_;
}
}
}
else
{
lean_dec_ref(v___y_4107_);
lean_dec_ref(v___y_4105_);
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
goto v___jp_4068_;
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___y_4107_);
lean_dec_ref(v___y_4105_);
v_a_4124_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4118_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4118_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
v___jp_4132_:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4136_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; uint8_t v___x_4148_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
v___x_4148_ = lean_unbox(v_a_4147_);
lean_dec(v_a_4147_);
if (v___x_4148_ == 0)
{
uint8_t v_ctor_4149_; 
v_ctor_4149_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*12 + 2);
if (v_ctor_4149_ == 0)
{
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
goto v___jp_4104_;
}
else
{
uint8_t v_ctor_4150_; 
v_ctor_4150_ = lean_ctor_get_uint8(v___y_4133_, sizeof(void*)*12 + 2);
if (v_ctor_4150_ == 0)
{
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
goto v___jp_4104_;
}
else
{
lean_object* v_self_4151_; lean_object* v_self_4152_; lean_object* v___x_4153_; 
v_self_4151_ = lean_ctor_get(v___y_4135_, 0);
v_self_4152_ = lean_ctor_get(v___y_4133_, 0);
lean_inc_ref(v_self_4152_);
lean_inc_ref(v_self_4151_);
v___x_4153_ = l_Lean_Meta_Grind_propagateCtor(v_self_4151_, v_self_4152_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_dec_ref_known(v___x_4153_, 1);
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
goto v___jp_4104_;
}
else
{
lean_dec_ref(v___y_4135_);
lean_dec_ref(v___y_4133_);
return v___x_4153_;
}
}
}
}
else
{
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
v___y_4112_ = v___y_4140_;
v___y_4113_ = v___y_4141_;
v___y_4114_ = v___y_4142_;
v___y_4115_ = v___y_4143_;
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
goto v___jp_4104_;
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref(v___y_4135_);
lean_dec_ref(v___y_4133_);
v_a_4154_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4146_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4146_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
v___jp_4162_:
{
if (v___y_4163_ == 0)
{
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
v___y_4136_ = v___y_4167_;
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
goto v___jp_4132_;
}
else
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_dec_ref_known(v___x_4177_, 1);
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
v___y_4136_ = v___y_4167_;
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
goto v___jp_4132_;
}
else
{
lean_dec_ref(v___y_4166_);
lean_dec_ref(v___y_4164_);
return v___x_4177_;
}
}
}
v___jp_4178_:
{
lean_object* v___x_4193_; 
lean_inc_ref(v___y_4192_);
lean_inc_ref(v___y_4190_);
v___x_4193_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4036_, v_isHEq_4037_, v_rhs_4035_, v_lhs_4034_, v_a_4057_, v_a_4054_, v___y_4190_, v___y_4192_, v___x_4067_, v___y_4183_, v___y_4180_, v___y_4191_, v___y_4188_, v___y_4179_, v___y_4185_, v___y_4181_, v___y_4189_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_dec_ref_known(v___x_4193_, 1);
v___y_4163_ = v___y_4184_;
v___y_4164_ = v___y_4190_;
v___y_4165_ = v___y_4182_;
v___y_4166_ = v___y_4192_;
v___y_4167_ = v___y_4183_;
v___y_4168_ = v___y_4180_;
v___y_4169_ = v___y_4191_;
v___y_4170_ = v___y_4188_;
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___y_4185_;
v___y_4173_ = v___y_4181_;
v___y_4174_ = v___y_4189_;
v___y_4175_ = v___y_4186_;
v___y_4176_ = v___y_4187_;
goto v___jp_4162_;
}
else
{
lean_dec_ref(v___y_4192_);
lean_dec_ref(v___y_4190_);
return v___x_4193_;
}
}
v___jp_4194_:
{
lean_object* v___x_4209_; 
lean_inc_ref(v___y_4206_);
lean_inc_ref(v___y_4208_);
v___x_4209_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4036_, v_isHEq_4037_, v_lhs_4034_, v_rhs_4035_, v_a_4054_, v_a_4057_, v___y_4208_, v___y_4206_, v___x_4062_, v___y_4199_, v___y_4196_, v___y_4207_, v___y_4204_, v___y_4195_, v___y_4201_, v___y_4197_, v___y_4205_, v___y_4202_, v___y_4203_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_dec_ref_known(v___x_4209_, 1);
v___y_4163_ = v___y_4200_;
v___y_4164_ = v___y_4206_;
v___y_4165_ = v___y_4198_;
v___y_4166_ = v___y_4208_;
v___y_4167_ = v___y_4199_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4207_;
v___y_4170_ = v___y_4204_;
v___y_4171_ = v___y_4195_;
v___y_4172_ = v___y_4201_;
v___y_4173_ = v___y_4197_;
v___y_4174_ = v___y_4205_;
v___y_4175_ = v___y_4202_;
v___y_4176_ = v___y_4203_;
goto v___jp_4162_;
}
else
{
lean_dec_ref(v___y_4208_);
lean_dec_ref(v___y_4206_);
return v___x_4209_;
}
}
v___jp_4210_:
{
lean_object* v_size_4228_; uint8_t v___x_4229_; 
v_size_4228_ = lean_ctor_get(v___y_4227_, 6);
v___x_4229_ = lean_nat_dec_lt(v_size_4224_, v_size_4228_);
lean_dec(v_size_4224_);
if (v___x_4229_ == 0)
{
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4222_;
v___y_4208_ = v___y_4227_;
goto v___jp_4194_;
}
else
{
if (v_interpreted_4225_ == 0)
{
if (v_ctor_4226_ == 0)
{
v___y_4179_ = v___y_4211_;
v___y_4180_ = v___y_4212_;
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4215_;
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4217_;
v___y_4186_ = v___y_4218_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4220_;
v___y_4189_ = v___y_4221_;
v___y_4190_ = v___y_4223_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4227_;
goto v___jp_4178_;
}
else
{
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4222_;
v___y_4208_ = v___y_4227_;
goto v___jp_4194_;
}
}
else
{
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4222_;
v___y_4208_ = v___y_4227_;
goto v___jp_4194_;
}
}
}
v___jp_4230_:
{
if (v_ctor_4245_ == 0)
{
lean_object* v_size_4246_; uint8_t v_interpreted_4247_; uint8_t v_ctor_4248_; 
v_size_4246_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4246_);
v_interpreted_4247_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v_ctor_4248_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___y_4232_;
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4243_;
v___y_4223_ = v___y_4242_;
v_size_4224_ = v_size_4246_;
v_interpreted_4225_ = v_interpreted_4247_;
v_ctor_4226_ = v_ctor_4248_;
v___y_4227_ = v___y_4244_;
goto v___jp_4210_;
}
else
{
uint8_t v_ctor_4249_; 
v_ctor_4249_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
if (v_ctor_4249_ == 0)
{
v___y_4179_ = v___y_4231_;
v___y_4180_ = v___y_4232_;
v___y_4181_ = v___y_4233_;
v___y_4182_ = v___y_4234_;
v___y_4183_ = v___y_4235_;
v___y_4184_ = v___y_4236_;
v___y_4185_ = v___y_4237_;
v___y_4186_ = v___y_4238_;
v___y_4187_ = v___y_4239_;
v___y_4188_ = v___y_4240_;
v___y_4189_ = v___y_4241_;
v___y_4190_ = v___y_4242_;
v___y_4191_ = v___y_4243_;
v___y_4192_ = v___y_4244_;
goto v___jp_4178_;
}
else
{
lean_object* v_size_4250_; uint8_t v_interpreted_4251_; 
v_size_4250_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4250_);
v_interpreted_4251_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___y_4232_;
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4243_;
v___y_4223_ = v___y_4242_;
v_size_4224_ = v_size_4250_;
v_interpreted_4225_ = v_interpreted_4251_;
v_ctor_4226_ = v_ctor_4249_;
v___y_4227_ = v___y_4244_;
goto v___jp_4210_;
}
}
}
v___jp_4252_:
{
uint8_t v_interpreted_4267_; 
v_interpreted_4267_ = lean_ctor_get_uint8(v___y_4254_, sizeof(void*)*12 + 1);
if (v_interpreted_4267_ == 0)
{
uint8_t v_ctor_4268_; 
v_ctor_4268_ = lean_ctor_get_uint8(v___y_4254_, sizeof(void*)*12 + 2);
v___y_4231_ = v___y_4261_;
v___y_4232_ = v___y_4258_;
v___y_4233_ = v___y_4263_;
v___y_4234_ = v_valueInconsistency_4255_;
v___y_4235_ = v___y_4257_;
v___y_4236_ = v_trueEqFalse_4256_;
v___y_4237_ = v___y_4262_;
v___y_4238_ = v___y_4265_;
v___y_4239_ = v___y_4266_;
v___y_4240_ = v___y_4260_;
v___y_4241_ = v___y_4264_;
v___y_4242_ = v___y_4253_;
v___y_4243_ = v___y_4259_;
v___y_4244_ = v___y_4254_;
v_ctor_4245_ = v_ctor_4268_;
goto v___jp_4230_;
}
else
{
uint8_t v_interpreted_4269_; 
v_interpreted_4269_ = lean_ctor_get_uint8(v___y_4253_, sizeof(void*)*12 + 1);
if (v_interpreted_4269_ == 0)
{
v___y_4179_ = v___y_4261_;
v___y_4180_ = v___y_4258_;
v___y_4181_ = v___y_4263_;
v___y_4182_ = v_valueInconsistency_4255_;
v___y_4183_ = v___y_4257_;
v___y_4184_ = v_trueEqFalse_4256_;
v___y_4185_ = v___y_4262_;
v___y_4186_ = v___y_4265_;
v___y_4187_ = v___y_4266_;
v___y_4188_ = v___y_4260_;
v___y_4189_ = v___y_4264_;
v___y_4190_ = v___y_4253_;
v___y_4191_ = v___y_4259_;
v___y_4192_ = v___y_4254_;
goto v___jp_4178_;
}
else
{
uint8_t v_ctor_4270_; 
v_ctor_4270_ = lean_ctor_get_uint8(v___y_4254_, sizeof(void*)*12 + 2);
v___y_4231_ = v___y_4261_;
v___y_4232_ = v___y_4258_;
v___y_4233_ = v___y_4263_;
v___y_4234_ = v_valueInconsistency_4255_;
v___y_4235_ = v___y_4257_;
v___y_4236_ = v_trueEqFalse_4256_;
v___y_4237_ = v___y_4262_;
v___y_4238_ = v___y_4265_;
v___y_4239_ = v___y_4266_;
v___y_4240_ = v___y_4260_;
v___y_4241_ = v___y_4264_;
v___y_4242_ = v___y_4253_;
v___y_4243_ = v___y_4259_;
v___y_4244_ = v___y_4254_;
v_ctor_4245_ = v_ctor_4270_;
goto v___jp_4230_;
}
}
}
v___jp_4271_:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4272_, v___y_4278_, v___y_4274_, v___y_4277_, v___y_4273_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_dec_ref_known(v___x_4284_, 1);
v___y_4253_ = v___y_4281_;
v___y_4254_ = v___y_4282_;
v_valueInconsistency_4255_ = v___x_4062_;
v_trueEqFalse_4256_ = v___x_4067_;
v___y_4257_ = v___y_4272_;
v___y_4258_ = v___y_4283_;
v___y_4259_ = v___y_4276_;
v___y_4260_ = v___y_4275_;
v___y_4261_ = v___y_4280_;
v___y_4262_ = v___y_4279_;
v___y_4263_ = v___y_4278_;
v___y_4264_ = v___y_4274_;
v___y_4265_ = v___y_4277_;
v___y_4266_ = v___y_4273_;
goto v___jp_4252_;
}
else
{
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
return v___x_4284_;
}
}
v___jp_4285_:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_Meta_Grind_hasSameType(v___y_4290_, v___y_4298_, v___y_4293_, v___y_4288_, v___y_4292_, v___y_4287_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; uint8_t v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = lean_unbox(v_a_4301_);
lean_dec(v_a_4301_);
if (v___x_4302_ == 0)
{
v___y_4253_ = v___y_4295_;
v___y_4254_ = v___y_4297_;
v_valueInconsistency_4255_ = v___x_4062_;
v_trueEqFalse_4256_ = v___x_4062_;
v___y_4257_ = v___y_4286_;
v___y_4258_ = v___y_4299_;
v___y_4259_ = v___y_4291_;
v___y_4260_ = v___y_4289_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4294_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4288_;
v___y_4265_ = v___y_4292_;
v___y_4266_ = v___y_4287_;
goto v___jp_4252_;
}
else
{
v___y_4253_ = v___y_4295_;
v___y_4254_ = v___y_4297_;
v_valueInconsistency_4255_ = v___x_4067_;
v_trueEqFalse_4256_ = v___x_4062_;
v___y_4257_ = v___y_4286_;
v___y_4258_ = v___y_4299_;
v___y_4259_ = v___y_4291_;
v___y_4260_ = v___y_4289_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4294_;
v___y_4263_ = v___y_4293_;
v___y_4264_ = v___y_4288_;
v___y_4265_ = v___y_4292_;
v___y_4266_ = v___y_4287_;
goto v___jp_4252_;
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4310_; 
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4295_);
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4303_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4305_ = v___x_4300_;
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4300_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4310_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
lean_object* v___x_4308_; 
if (v_isShared_4306_ == 0)
{
v___x_4308_ = v___x_4305_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
v___jp_4311_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_st_ref_get(v___y_4312_);
lean_inc_ref(v_root_4058_);
v___x_4323_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4322_, v_root_4058_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___x_4322_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v___x_4325_ = lean_st_ref_get(v___y_4312_);
lean_inc_ref(v_root_4059_);
v___x_4326_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4325_, v_root_4059_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___x_4325_);
if (lean_obj_tag(v___x_4326_) == 0)
{
uint8_t v_interpreted_4327_; 
v_interpreted_4327_ = lean_ctor_get_uint8(v_a_4324_, sizeof(void*)*12 + 1);
if (v_interpreted_4327_ == 0)
{
lean_object* v_a_4328_; uint8_t v_ctor_4329_; 
v_a_4328_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4326_, 1);
v_ctor_4329_ = lean_ctor_get_uint8(v_a_4324_, sizeof(void*)*12 + 2);
v___y_4231_ = v___y_4316_;
v___y_4232_ = v___y_4313_;
v___y_4233_ = v___y_4318_;
v___y_4234_ = v___x_4062_;
v___y_4235_ = v___y_4312_;
v___y_4236_ = v___x_4062_;
v___y_4237_ = v___y_4317_;
v___y_4238_ = v___y_4320_;
v___y_4239_ = v___y_4321_;
v___y_4240_ = v___y_4315_;
v___y_4241_ = v___y_4319_;
v___y_4242_ = v_a_4328_;
v___y_4243_ = v___y_4314_;
v___y_4244_ = v_a_4324_;
v_ctor_4245_ = v_ctor_4329_;
goto v___jp_4230_;
}
else
{
lean_object* v_a_4330_; uint8_t v_interpreted_4331_; 
v_a_4330_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4326_, 1);
v_interpreted_4331_ = lean_ctor_get_uint8(v_a_4330_, sizeof(void*)*12 + 1);
if (v_interpreted_4331_ == 0)
{
v___y_4179_ = v___y_4316_;
v___y_4180_ = v___y_4313_;
v___y_4181_ = v___y_4318_;
v___y_4182_ = v___x_4062_;
v___y_4183_ = v___y_4312_;
v___y_4184_ = v___x_4062_;
v___y_4185_ = v___y_4317_;
v___y_4186_ = v___y_4320_;
v___y_4187_ = v___y_4321_;
v___y_4188_ = v___y_4315_;
v___y_4189_ = v___y_4319_;
v___y_4190_ = v_a_4330_;
v___y_4191_ = v___y_4314_;
v___y_4192_ = v_a_4324_;
goto v___jp_4178_;
}
else
{
lean_object* v_self_4332_; uint8_t v_ctor_4333_; uint8_t v_heqProofs_4334_; lean_object* v_self_4335_; uint8_t v_heqProofs_4336_; uint8_t v___x_4337_; 
v_self_4332_ = lean_ctor_get(v_a_4324_, 0);
v_ctor_4333_ = lean_ctor_get_uint8(v_a_4324_, sizeof(void*)*12 + 2);
v_heqProofs_4334_ = lean_ctor_get_uint8(v_a_4324_, sizeof(void*)*12 + 4);
v_self_4335_ = lean_ctor_get(v_a_4330_, 0);
v_heqProofs_4336_ = lean_ctor_get_uint8(v_a_4330_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4058_);
v___x_4337_ = l_Lean_Expr_isTrue(v_root_4058_);
if (v___x_4337_ == 0)
{
uint8_t v___x_4338_; 
lean_inc_ref(v_root_4059_);
v___x_4338_ = l_Lean_Expr_isTrue(v_root_4059_);
if (v___x_4338_ == 0)
{
if (v_isHEq_4037_ == 0)
{
if (v_heqProofs_4334_ == 0)
{
if (v_heqProofs_4336_ == 0)
{
v___y_4231_ = v___y_4316_;
v___y_4232_ = v___y_4313_;
v___y_4233_ = v___y_4318_;
v___y_4234_ = v___x_4067_;
v___y_4235_ = v___y_4312_;
v___y_4236_ = v___x_4062_;
v___y_4237_ = v___y_4317_;
v___y_4238_ = v___y_4320_;
v___y_4239_ = v___y_4321_;
v___y_4240_ = v___y_4315_;
v___y_4241_ = v___y_4319_;
v___y_4242_ = v_a_4330_;
v___y_4243_ = v___y_4314_;
v___y_4244_ = v_a_4324_;
v_ctor_4245_ = v_ctor_4333_;
goto v___jp_4230_;
}
else
{
lean_inc_ref(v_self_4335_);
lean_inc_ref(v_self_4332_);
v___y_4286_ = v___y_4312_;
v___y_4287_ = v___y_4321_;
v___y_4288_ = v___y_4319_;
v___y_4289_ = v___y_4315_;
v___y_4290_ = v_self_4332_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4318_;
v___y_4294_ = v___y_4317_;
v___y_4295_ = v_a_4330_;
v___y_4296_ = v___y_4316_;
v___y_4297_ = v_a_4324_;
v___y_4298_ = v_self_4335_;
v___y_4299_ = v___y_4313_;
goto v___jp_4285_;
}
}
else
{
lean_inc_ref(v_self_4335_);
lean_inc_ref(v_self_4332_);
v___y_4286_ = v___y_4312_;
v___y_4287_ = v___y_4321_;
v___y_4288_ = v___y_4319_;
v___y_4289_ = v___y_4315_;
v___y_4290_ = v_self_4332_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4318_;
v___y_4294_ = v___y_4317_;
v___y_4295_ = v_a_4330_;
v___y_4296_ = v___y_4316_;
v___y_4297_ = v_a_4324_;
v___y_4298_ = v_self_4335_;
v___y_4299_ = v___y_4313_;
goto v___jp_4285_;
}
}
else
{
lean_inc_ref(v_self_4335_);
lean_inc_ref(v_self_4332_);
v___y_4286_ = v___y_4312_;
v___y_4287_ = v___y_4321_;
v___y_4288_ = v___y_4319_;
v___y_4289_ = v___y_4315_;
v___y_4290_ = v_self_4332_;
v___y_4291_ = v___y_4314_;
v___y_4292_ = v___y_4320_;
v___y_4293_ = v___y_4318_;
v___y_4294_ = v___y_4317_;
v___y_4295_ = v_a_4330_;
v___y_4296_ = v___y_4316_;
v___y_4297_ = v_a_4324_;
v___y_4298_ = v_self_4335_;
v___y_4299_ = v___y_4313_;
goto v___jp_4285_;
}
}
else
{
v___y_4272_ = v___y_4312_;
v___y_4273_ = v___y_4321_;
v___y_4274_ = v___y_4319_;
v___y_4275_ = v___y_4315_;
v___y_4276_ = v___y_4314_;
v___y_4277_ = v___y_4320_;
v___y_4278_ = v___y_4318_;
v___y_4279_ = v___y_4317_;
v___y_4280_ = v___y_4316_;
v___y_4281_ = v_a_4330_;
v___y_4282_ = v_a_4324_;
v___y_4283_ = v___y_4313_;
goto v___jp_4271_;
}
}
else
{
v___y_4272_ = v___y_4312_;
v___y_4273_ = v___y_4321_;
v___y_4274_ = v___y_4319_;
v___y_4275_ = v___y_4315_;
v___y_4276_ = v___y_4314_;
v___y_4277_ = v___y_4320_;
v___y_4278_ = v___y_4318_;
v___y_4279_ = v___y_4317_;
v___y_4280_ = v___y_4316_;
v___y_4281_ = v_a_4330_;
v___y_4282_ = v_a_4324_;
v___y_4283_ = v___y_4313_;
goto v___jp_4271_;
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_a_4324_);
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4339_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4326_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4326_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4347_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4323_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4323_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
else
{
lean_object* v_toCold_4393_; lean_object* v_options_4394_; uint8_t v_hasTrace_4395_; 
lean_dec(v_a_4057_);
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
v_toCold_4393_ = lean_ctor_get(v_a_4046_, 0);
v_options_4394_ = lean_ctor_get(v_toCold_4393_, 2);
v_hasTrace_4395_ = lean_ctor_get_uint8(v_options_4394_, sizeof(void*)*1);
if (v_hasTrace_4395_ == 0)
{
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
goto v___jp_4049_;
}
else
{
lean_object* v_inheritedTraceOptions_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_inheritedTraceOptions_4396_ = lean_ctor_get(v_toCold_4393_, 11);
v___x_4397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4396_, v_options_4394_, v___x_4398_);
if (v___x_4399_ == 0)
{
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
goto v___jp_4049_;
}
else
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Meta_Grind_updateLastTag(v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v___x_4401_; 
lean_dec_ref_known(v___x_4400_, 1);
v___x_4401_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4034_, v_a_4038_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4035_, v_a_4038_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v_a_4402_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
lean_ctor_set(v___x_4407_, 1, v_a_4404_);
v___x_4408_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4397_, v___x_4409_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_dec_ref_known(v___x_4410_, 1);
goto v___jp_4049_;
}
else
{
return v___x_4410_;
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4402_);
v_a_4411_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4403_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4403_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec_ref(v_rhs_4035_);
v_a_4419_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4401_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4401_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
return v___x_4400_;
}
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_a_4054_);
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4427_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4056_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4056_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref(v_proof_4036_);
lean_dec_ref(v_rhs_4035_);
lean_dec_ref(v_lhs_4034_);
v_a_4435_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4053_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4053_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
v___jp_4049_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_box(0);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4443_, lean_object* v_rhs_4444_, lean_object* v_proof_4445_, lean_object* v_isHEq_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_){
_start:
{
uint8_t v_isHEq_boxed_4458_; lean_object* v_res_4459_; 
v_isHEq_boxed_4458_ = lean_unbox(v_isHEq_4446_);
v_res_4459_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4443_, v_rhs_4444_, v_proof_4445_, v_isHEq_boxed_4458_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec(v_a_4447_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v_toGoalState_4465_; lean_object* v_mvarId_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4503_; 
v___x_4464_ = lean_st_ref_take(v_a_4462_);
v_toGoalState_4465_ = lean_ctor_get(v___x_4464_, 0);
v_mvarId_4466_ = lean_ctor_get(v___x_4464_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4468_ = v___x_4464_;
v_isShared_4469_ = v_isSharedCheck_4503_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_mvarId_4466_);
lean_inc(v_toGoalState_4465_);
lean_dec(v___x_4464_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4503_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v_nextDeclIdx_4470_; lean_object* v_enodeMap_4471_; lean_object* v_exprs_4472_; lean_object* v_parents_4473_; lean_object* v_congrTable_4474_; lean_object* v_appMap_4475_; lean_object* v_indicesFound_4476_; lean_object* v_internalizing_4477_; uint8_t v_inconsistent_4478_; lean_object* v_nextIdx_4479_; lean_object* v_newRawFacts_4480_; lean_object* v_facts_4481_; lean_object* v_extThms_4482_; lean_object* v_ematch_4483_; lean_object* v_inj_4484_; lean_object* v_split_4485_; lean_object* v_clean_4486_; lean_object* v_sstates_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4501_; 
v_nextDeclIdx_4470_ = lean_ctor_get(v_toGoalState_4465_, 0);
v_enodeMap_4471_ = lean_ctor_get(v_toGoalState_4465_, 1);
v_exprs_4472_ = lean_ctor_get(v_toGoalState_4465_, 2);
v_parents_4473_ = lean_ctor_get(v_toGoalState_4465_, 3);
v_congrTable_4474_ = lean_ctor_get(v_toGoalState_4465_, 4);
v_appMap_4475_ = lean_ctor_get(v_toGoalState_4465_, 5);
v_indicesFound_4476_ = lean_ctor_get(v_toGoalState_4465_, 6);
v_internalizing_4477_ = lean_ctor_get(v_toGoalState_4465_, 8);
v_inconsistent_4478_ = lean_ctor_get_uint8(v_toGoalState_4465_, sizeof(void*)*18);
v_nextIdx_4479_ = lean_ctor_get(v_toGoalState_4465_, 9);
v_newRawFacts_4480_ = lean_ctor_get(v_toGoalState_4465_, 10);
v_facts_4481_ = lean_ctor_get(v_toGoalState_4465_, 11);
v_extThms_4482_ = lean_ctor_get(v_toGoalState_4465_, 12);
v_ematch_4483_ = lean_ctor_get(v_toGoalState_4465_, 13);
v_inj_4484_ = lean_ctor_get(v_toGoalState_4465_, 14);
v_split_4485_ = lean_ctor_get(v_toGoalState_4465_, 15);
v_clean_4486_ = lean_ctor_get(v_toGoalState_4465_, 16);
v_sstates_4487_ = lean_ctor_get(v_toGoalState_4465_, 17);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_toGoalState_4465_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v_toGoalState_4465_, 7);
lean_dec(v_unused_4502_);
v___x_4489_ = v_toGoalState_4465_;
v_isShared_4490_ = v_isSharedCheck_4501_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_sstates_4487_);
lean_inc(v_clean_4486_);
lean_inc(v_split_4485_);
lean_inc(v_inj_4484_);
lean_inc(v_ematch_4483_);
lean_inc(v_extThms_4482_);
lean_inc(v_facts_4481_);
lean_inc(v_newRawFacts_4480_);
lean_inc(v_nextIdx_4479_);
lean_inc(v_internalizing_4477_);
lean_inc(v_indicesFound_4476_);
lean_inc(v_appMap_4475_);
lean_inc(v_congrTable_4474_);
lean_inc(v_parents_4473_);
lean_inc(v_exprs_4472_);
lean_inc(v_enodeMap_4471_);
lean_inc(v_nextDeclIdx_4470_);
lean_dec(v_toGoalState_4465_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4501_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4491_ = lean_box(0);
v___x_4492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 7, v___x_4492_);
v___x_4494_ = v___x_4489_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_nextDeclIdx_4470_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_enodeMap_4471_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_exprs_4472_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_parents_4473_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_congrTable_4474_);
lean_ctor_set(v_reuseFailAlloc_4500_, 5, v_appMap_4475_);
lean_ctor_set(v_reuseFailAlloc_4500_, 6, v_indicesFound_4476_);
lean_ctor_set(v_reuseFailAlloc_4500_, 7, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4500_, 8, v_internalizing_4477_);
lean_ctor_set(v_reuseFailAlloc_4500_, 9, v_nextIdx_4479_);
lean_ctor_set(v_reuseFailAlloc_4500_, 10, v_newRawFacts_4480_);
lean_ctor_set(v_reuseFailAlloc_4500_, 11, v_facts_4481_);
lean_ctor_set(v_reuseFailAlloc_4500_, 12, v_extThms_4482_);
lean_ctor_set(v_reuseFailAlloc_4500_, 13, v_ematch_4483_);
lean_ctor_set(v_reuseFailAlloc_4500_, 14, v_inj_4484_);
lean_ctor_set(v_reuseFailAlloc_4500_, 15, v_split_4485_);
lean_ctor_set(v_reuseFailAlloc_4500_, 16, v_clean_4486_);
lean_ctor_set(v_reuseFailAlloc_4500_, 17, v_sstates_4487_);
lean_ctor_set_uint8(v_reuseFailAlloc_4500_, sizeof(void*)*18, v_inconsistent_4478_);
v___x_4494_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4496_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v___x_4494_);
v___x_4496_ = v___x_4468_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_mvarId_4466_);
v___x_4496_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = lean_st_ref_put(v_a_4462_, v___x_4496_);
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4491_);
return v___x_4498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4504_);
lean_dec(v_a_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4507_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec(v_a_4519_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4531_){
_start:
{
lean_object* v___x_4533_; lean_object* v_toGoalState_4534_; lean_object* v_toProcess_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4533_ = lean_st_ref_get(v_a_4531_);
v_toGoalState_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc_ref(v_toGoalState_4534_);
lean_dec(v___x_4533_);
v_toProcess_4535_ = lean_ctor_get(v_toGoalState_4534_, 7);
lean_inc_ref(v_toProcess_4535_);
lean_dec_ref(v_toGoalState_4534_);
v___x_4536_ = lean_array_get_size(v_toProcess_4535_);
v___x_4537_ = lean_unsigned_to_nat(1u);
v___x_4538_ = lean_nat_sub(v___x_4536_, v___x_4537_);
v___x_4539_ = lean_nat_dec_lt(v___x_4538_, v___x_4536_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
lean_dec(v___x_4538_);
lean_dec_ref(v_toProcess_4535_);
v___x_4540_ = lean_box(0);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
else
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v_toGoalState_4545_; lean_object* v_mvarId_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4582_; 
v___x_4542_ = lean_array_fget(v_toProcess_4535_, v___x_4538_);
lean_dec(v___x_4538_);
lean_dec_ref(v_toProcess_4535_);
v___x_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
v___x_4544_ = lean_st_ref_take(v_a_4531_);
v_toGoalState_4545_ = lean_ctor_get(v___x_4544_, 0);
v_mvarId_4546_ = lean_ctor_get(v___x_4544_, 1);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4548_ = v___x_4544_;
v_isShared_4549_ = v_isSharedCheck_4582_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_mvarId_4546_);
lean_inc(v_toGoalState_4545_);
lean_dec(v___x_4544_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4582_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v_nextDeclIdx_4550_; lean_object* v_enodeMap_4551_; lean_object* v_exprs_4552_; lean_object* v_parents_4553_; lean_object* v_congrTable_4554_; lean_object* v_appMap_4555_; lean_object* v_indicesFound_4556_; lean_object* v_toProcess_4557_; lean_object* v_internalizing_4558_; uint8_t v_inconsistent_4559_; lean_object* v_nextIdx_4560_; lean_object* v_newRawFacts_4561_; lean_object* v_facts_4562_; lean_object* v_extThms_4563_; lean_object* v_ematch_4564_; lean_object* v_inj_4565_; lean_object* v_split_4566_; lean_object* v_clean_4567_; lean_object* v_sstates_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4581_; 
v_nextDeclIdx_4550_ = lean_ctor_get(v_toGoalState_4545_, 0);
v_enodeMap_4551_ = lean_ctor_get(v_toGoalState_4545_, 1);
v_exprs_4552_ = lean_ctor_get(v_toGoalState_4545_, 2);
v_parents_4553_ = lean_ctor_get(v_toGoalState_4545_, 3);
v_congrTable_4554_ = lean_ctor_get(v_toGoalState_4545_, 4);
v_appMap_4555_ = lean_ctor_get(v_toGoalState_4545_, 5);
v_indicesFound_4556_ = lean_ctor_get(v_toGoalState_4545_, 6);
v_toProcess_4557_ = lean_ctor_get(v_toGoalState_4545_, 7);
v_internalizing_4558_ = lean_ctor_get(v_toGoalState_4545_, 8);
v_inconsistent_4559_ = lean_ctor_get_uint8(v_toGoalState_4545_, sizeof(void*)*18);
v_nextIdx_4560_ = lean_ctor_get(v_toGoalState_4545_, 9);
v_newRawFacts_4561_ = lean_ctor_get(v_toGoalState_4545_, 10);
v_facts_4562_ = lean_ctor_get(v_toGoalState_4545_, 11);
v_extThms_4563_ = lean_ctor_get(v_toGoalState_4545_, 12);
v_ematch_4564_ = lean_ctor_get(v_toGoalState_4545_, 13);
v_inj_4565_ = lean_ctor_get(v_toGoalState_4545_, 14);
v_split_4566_ = lean_ctor_get(v_toGoalState_4545_, 15);
v_clean_4567_ = lean_ctor_get(v_toGoalState_4545_, 16);
v_sstates_4568_ = lean_ctor_get(v_toGoalState_4545_, 17);
v_isSharedCheck_4581_ = !lean_is_exclusive(v_toGoalState_4545_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4570_ = v_toGoalState_4545_;
v_isShared_4571_ = v_isSharedCheck_4581_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_sstates_4568_);
lean_inc(v_clean_4567_);
lean_inc(v_split_4566_);
lean_inc(v_inj_4565_);
lean_inc(v_ematch_4564_);
lean_inc(v_extThms_4563_);
lean_inc(v_facts_4562_);
lean_inc(v_newRawFacts_4561_);
lean_inc(v_nextIdx_4560_);
lean_inc(v_internalizing_4558_);
lean_inc(v_toProcess_4557_);
lean_inc(v_indicesFound_4556_);
lean_inc(v_appMap_4555_);
lean_inc(v_congrTable_4554_);
lean_inc(v_parents_4553_);
lean_inc(v_exprs_4552_);
lean_inc(v_enodeMap_4551_);
lean_inc(v_nextDeclIdx_4550_);
lean_dec(v_toGoalState_4545_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4581_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4572_ = lean_array_pop(v_toProcess_4557_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 7, v___x_4572_);
v___x_4574_ = v___x_4570_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_nextDeclIdx_4550_);
lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_enodeMap_4551_);
lean_ctor_set(v_reuseFailAlloc_4580_, 2, v_exprs_4552_);
lean_ctor_set(v_reuseFailAlloc_4580_, 3, v_parents_4553_);
lean_ctor_set(v_reuseFailAlloc_4580_, 4, v_congrTable_4554_);
lean_ctor_set(v_reuseFailAlloc_4580_, 5, v_appMap_4555_);
lean_ctor_set(v_reuseFailAlloc_4580_, 6, v_indicesFound_4556_);
lean_ctor_set(v_reuseFailAlloc_4580_, 7, v___x_4572_);
lean_ctor_set(v_reuseFailAlloc_4580_, 8, v_internalizing_4558_);
lean_ctor_set(v_reuseFailAlloc_4580_, 9, v_nextIdx_4560_);
lean_ctor_set(v_reuseFailAlloc_4580_, 10, v_newRawFacts_4561_);
lean_ctor_set(v_reuseFailAlloc_4580_, 11, v_facts_4562_);
lean_ctor_set(v_reuseFailAlloc_4580_, 12, v_extThms_4563_);
lean_ctor_set(v_reuseFailAlloc_4580_, 13, v_ematch_4564_);
lean_ctor_set(v_reuseFailAlloc_4580_, 14, v_inj_4565_);
lean_ctor_set(v_reuseFailAlloc_4580_, 15, v_split_4566_);
lean_ctor_set(v_reuseFailAlloc_4580_, 16, v_clean_4567_);
lean_ctor_set(v_reuseFailAlloc_4580_, 17, v_sstates_4568_);
lean_ctor_set_uint8(v_reuseFailAlloc_4580_, sizeof(void*)*18, v_inconsistent_4559_);
v___x_4574_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4576_; 
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v___x_4574_);
v___x_4576_ = v___x_4548_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4574_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_mvarId_4546_);
v___x_4576_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4577_ = lean_st_ref_put(v_a_4531_, v___x_4576_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4543_);
return v___x_4578_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4583_);
lean_dec(v_a_4583_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4586_);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec(v_a_4598_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4610_, lean_object* v_rhs_4611_, lean_object* v_proof_4612_, uint8_t v_isHEq_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_){
_start:
{
lean_object* v___x_4625_; 
v___x_4625_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4610_, v_rhs_4611_, v_proof_4612_, v_isHEq_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v___x_4626_; 
lean_dec_ref_known(v___x_4625_, 1);
lean_inc(v_a_4623_);
lean_inc_ref(v_a_4622_);
lean_inc(v_a_4621_);
lean_inc_ref(v_a_4620_);
lean_inc(v_a_4619_);
lean_inc_ref(v_a_4618_);
lean_inc(v_a_4617_);
lean_inc_ref(v_a_4616_);
lean_inc(v_a_4615_);
lean_inc(v_a_4614_);
v___x_4626_ = lean_grind_process_to_do(v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
return v___x_4626_;
}
else
{
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4627_, lean_object* v_rhs_4628_, lean_object* v_proof_4629_, lean_object* v_isHEq_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_){
_start:
{
uint8_t v_isHEq_boxed_4642_; lean_object* v_res_4643_; 
v_isHEq_boxed_4642_ = lean_unbox(v_isHEq_4630_);
v_res_4643_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4627_, v_rhs_4628_, v_proof_4629_, v_isHEq_boxed_4642_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
lean_dec(v_a_4640_);
lean_dec_ref(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec(v_a_4631_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4644_, lean_object* v_rhs_4645_, lean_object* v_proof_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
uint8_t v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = 0;
v___x_4659_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4644_, v_rhs_4645_, v_proof_4646_, v___x_4658_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4660_, lean_object* v_rhs_4661_, lean_object* v_proof_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4660_, v_rhs_4661_, v_proof_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec(v_a_4663_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4675_, lean_object* v_rhs_4676_, lean_object* v_proof_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
uint8_t v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = 1;
v___x_4690_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4675_, v_rhs_4676_, v_proof_4677_, v___x_4689_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_);
return v___x_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4691_, lean_object* v_rhs_4692_, lean_object* v_proof_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4691_, v_rhs_4692_, v_proof_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec(v_a_4694_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v___x_4709_; lean_object* v_toGoalState_4710_; lean_object* v_mvarId_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4748_; 
v___x_4709_ = lean_st_ref_take(v_a_4707_);
v_toGoalState_4710_ = lean_ctor_get(v___x_4709_, 0);
v_mvarId_4711_ = lean_ctor_get(v___x_4709_, 1);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4713_ = v___x_4709_;
v_isShared_4714_ = v_isSharedCheck_4748_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_mvarId_4711_);
lean_inc(v_toGoalState_4710_);
lean_dec(v___x_4709_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4748_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v_nextDeclIdx_4715_; lean_object* v_enodeMap_4716_; lean_object* v_exprs_4717_; lean_object* v_parents_4718_; lean_object* v_congrTable_4719_; lean_object* v_appMap_4720_; lean_object* v_indicesFound_4721_; lean_object* v_toProcess_4722_; lean_object* v_internalizing_4723_; uint8_t v_inconsistent_4724_; lean_object* v_nextIdx_4725_; lean_object* v_newRawFacts_4726_; lean_object* v_facts_4727_; lean_object* v_extThms_4728_; lean_object* v_ematch_4729_; lean_object* v_inj_4730_; lean_object* v_split_4731_; lean_object* v_clean_4732_; lean_object* v_sstates_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4747_; 
v_nextDeclIdx_4715_ = lean_ctor_get(v_toGoalState_4710_, 0);
v_enodeMap_4716_ = lean_ctor_get(v_toGoalState_4710_, 1);
v_exprs_4717_ = lean_ctor_get(v_toGoalState_4710_, 2);
v_parents_4718_ = lean_ctor_get(v_toGoalState_4710_, 3);
v_congrTable_4719_ = lean_ctor_get(v_toGoalState_4710_, 4);
v_appMap_4720_ = lean_ctor_get(v_toGoalState_4710_, 5);
v_indicesFound_4721_ = lean_ctor_get(v_toGoalState_4710_, 6);
v_toProcess_4722_ = lean_ctor_get(v_toGoalState_4710_, 7);
v_internalizing_4723_ = lean_ctor_get(v_toGoalState_4710_, 8);
v_inconsistent_4724_ = lean_ctor_get_uint8(v_toGoalState_4710_, sizeof(void*)*18);
v_nextIdx_4725_ = lean_ctor_get(v_toGoalState_4710_, 9);
v_newRawFacts_4726_ = lean_ctor_get(v_toGoalState_4710_, 10);
v_facts_4727_ = lean_ctor_get(v_toGoalState_4710_, 11);
v_extThms_4728_ = lean_ctor_get(v_toGoalState_4710_, 12);
v_ematch_4729_ = lean_ctor_get(v_toGoalState_4710_, 13);
v_inj_4730_ = lean_ctor_get(v_toGoalState_4710_, 14);
v_split_4731_ = lean_ctor_get(v_toGoalState_4710_, 15);
v_clean_4732_ = lean_ctor_get(v_toGoalState_4710_, 16);
v_sstates_4733_ = lean_ctor_get(v_toGoalState_4710_, 17);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_toGoalState_4710_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4735_ = v_toGoalState_4710_;
v_isShared_4736_ = v_isSharedCheck_4747_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_sstates_4733_);
lean_inc(v_clean_4732_);
lean_inc(v_split_4731_);
lean_inc(v_inj_4730_);
lean_inc(v_ematch_4729_);
lean_inc(v_extThms_4728_);
lean_inc(v_facts_4727_);
lean_inc(v_newRawFacts_4726_);
lean_inc(v_nextIdx_4725_);
lean_inc(v_internalizing_4723_);
lean_inc(v_toProcess_4722_);
lean_inc(v_indicesFound_4721_);
lean_inc(v_appMap_4720_);
lean_inc(v_congrTable_4719_);
lean_inc(v_parents_4718_);
lean_inc(v_exprs_4717_);
lean_inc(v_enodeMap_4716_);
lean_inc(v_nextDeclIdx_4715_);
lean_dec(v_toGoalState_4710_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4747_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4737_ = lean_box(0);
v___x_4738_ = l_Lean_PersistentArray_push___redArg(v_facts_4727_, v_fact_4706_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 11, v___x_4738_);
v___x_4740_ = v___x_4735_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_nextDeclIdx_4715_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_enodeMap_4716_);
lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_exprs_4717_);
lean_ctor_set(v_reuseFailAlloc_4746_, 3, v_parents_4718_);
lean_ctor_set(v_reuseFailAlloc_4746_, 4, v_congrTable_4719_);
lean_ctor_set(v_reuseFailAlloc_4746_, 5, v_appMap_4720_);
lean_ctor_set(v_reuseFailAlloc_4746_, 6, v_indicesFound_4721_);
lean_ctor_set(v_reuseFailAlloc_4746_, 7, v_toProcess_4722_);
lean_ctor_set(v_reuseFailAlloc_4746_, 8, v_internalizing_4723_);
lean_ctor_set(v_reuseFailAlloc_4746_, 9, v_nextIdx_4725_);
lean_ctor_set(v_reuseFailAlloc_4746_, 10, v_newRawFacts_4726_);
lean_ctor_set(v_reuseFailAlloc_4746_, 11, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4746_, 12, v_extThms_4728_);
lean_ctor_set(v_reuseFailAlloc_4746_, 13, v_ematch_4729_);
lean_ctor_set(v_reuseFailAlloc_4746_, 14, v_inj_4730_);
lean_ctor_set(v_reuseFailAlloc_4746_, 15, v_split_4731_);
lean_ctor_set(v_reuseFailAlloc_4746_, 16, v_clean_4732_);
lean_ctor_set(v_reuseFailAlloc_4746_, 17, v_sstates_4733_);
lean_ctor_set_uint8(v_reuseFailAlloc_4746_, sizeof(void*)*18, v_inconsistent_4724_);
v___x_4740_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4742_; 
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 0, v___x_4740_);
v___x_4742_ = v___x_4713_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4740_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_mvarId_4711_);
v___x_4742_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_st_ref_put(v_a_4707_, v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4737_);
return v___x_4744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4749_, v_a_4750_);
lean_dec(v_a_4750_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4753_, v_a_4754_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec(v_a_4767_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4779_, lean_object* v_rhs_4780_, lean_object* v_proof_4781_, lean_object* v_generation_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_){
_start:
{
lean_object* v___x_4794_; 
lean_inc_ref(v_rhs_4780_);
lean_inc_ref(v_lhs_4779_);
v___x_4794_ = l_Lean_Meta_mkEq(v_lhs_4779_, v_rhs_4780_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4806_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc_n(v_a_4795_, 2);
lean_dec_ref_known(v___x_4794_, 1);
v___x_4796_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4795_, v_a_4783_);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v___x_4796_, 0);
lean_dec(v_unused_4807_);
v___x_4798_ = v___x_4796_;
v_isShared_4799_ = v_isSharedCheck_4806_;
goto v_resetjp_4797_;
}
else
{
lean_dec(v___x_4796_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4806_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
lean_ctor_set_tag(v___x_4798_, 1);
lean_ctor_set(v___x_4798_, 0, v_a_4795_);
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4795_);
v___x_4801_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; 
lean_inc(v_a_4792_);
lean_inc_ref(v_a_4791_);
lean_inc(v_a_4790_);
lean_inc_ref(v_a_4789_);
lean_inc(v_a_4788_);
lean_inc_ref(v_a_4787_);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc(v_a_4783_);
lean_inc_ref(v___x_4801_);
lean_inc(v_generation_4782_);
lean_inc_ref(v_lhs_4779_);
v___x_4802_ = lean_grind_internalize(v_lhs_4779_, v_generation_4782_, v___x_4801_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v___x_4803_; 
lean_dec_ref_known(v___x_4802_, 1);
lean_inc(v_a_4792_);
lean_inc_ref(v_a_4791_);
lean_inc(v_a_4790_);
lean_inc_ref(v_a_4789_);
lean_inc(v_a_4788_);
lean_inc_ref(v_a_4787_);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc(v_a_4783_);
lean_inc_ref(v_rhs_4780_);
v___x_4803_ = lean_grind_internalize(v_rhs_4780_, v_generation_4782_, v___x_4801_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v___x_4804_; 
lean_dec_ref_known(v___x_4803_, 1);
v___x_4804_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4779_, v_rhs_4780_, v_proof_4781_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_);
return v___x_4804_;
}
else
{
lean_dec_ref(v_proof_4781_);
lean_dec_ref(v_rhs_4780_);
lean_dec_ref(v_lhs_4779_);
return v___x_4803_;
}
}
else
{
lean_dec_ref(v___x_4801_);
lean_dec(v_generation_4782_);
lean_dec_ref(v_proof_4781_);
lean_dec_ref(v_rhs_4780_);
lean_dec_ref(v_lhs_4779_);
return v___x_4802_;
}
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_generation_4782_);
lean_dec_ref(v_proof_4781_);
lean_dec_ref(v_rhs_4780_);
lean_dec_ref(v_lhs_4779_);
v_a_4808_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4794_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4794_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4816_, lean_object* v_rhs_4817_, lean_object* v_proof_4818_, lean_object* v_generation_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4816_, v_rhs_4817_, v_proof_4818_, v_generation_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec(v_a_4820_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4832_, lean_object* v_generation_4833_, lean_object* v_p_4834_, uint8_t v_isNeg_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = lean_box(0);
lean_inc(v_a_4845_);
lean_inc_ref(v_a_4844_);
lean_inc(v_a_4843_);
lean_inc_ref(v_a_4842_);
lean_inc(v_a_4841_);
lean_inc_ref(v_a_4840_);
lean_inc(v_a_4839_);
lean_inc_ref(v_a_4838_);
lean_inc(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_p_4834_);
v___x_4848_ = lean_grind_internalize(v_p_4834_, v_generation_4833_, v___x_4847_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_dec_ref_known(v___x_4848_, 1);
if (v_isNeg_4835_ == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4840_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
v___x_4851_ = l_Lean_Meta_mkEqTrue(v_proof_4832_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v___x_4853_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4834_, v_a_4850_, v_a_4852_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
return v___x_4853_;
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec(v_a_4850_);
lean_dec_ref(v_p_4834_);
v_a_4854_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4851_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4851_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_dec_ref(v_p_4834_);
lean_dec_ref(v_proof_4832_);
v_a_4862_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4849_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4849_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
else
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4840_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4872_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_a_4871_);
lean_dec_ref_known(v___x_4870_, 1);
v___x_4872_ = l_Lean_Meta_mkEqFalse(v_proof_4832_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
v___x_4874_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4834_, v_a_4871_, v_a_4873_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_);
return v___x_4874_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
lean_dec(v_a_4871_);
lean_dec_ref(v_p_4834_);
v_a_4875_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4872_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4872_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec_ref(v_p_4834_);
lean_dec_ref(v_proof_4832_);
v_a_4883_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4870_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4870_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4834_);
lean_dec_ref(v_proof_4832_);
return v___x_4848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4891_, lean_object* v_generation_4892_, lean_object* v_p_4893_, lean_object* v_isNeg_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_){
_start:
{
uint8_t v_isNeg_boxed_4906_; lean_object* v_res_4907_; 
v_isNeg_boxed_4906_ = lean_unbox(v_isNeg_4894_);
v_res_4907_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4891_, v_generation_4892_, v_p_4893_, v_isNeg_boxed_4906_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
lean_dec(v_a_4904_);
lean_dec_ref(v_a_4903_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
lean_dec(v_a_4896_);
lean_dec(v_a_4895_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4908_, lean_object* v_generation_4909_, lean_object* v_p_4910_, lean_object* v_lhs_4911_, lean_object* v_rhs_4912_, uint8_t v_isNeg_4913_, uint8_t v_isHEq_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_){
_start:
{
if (v_isNeg_4913_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_inc_ref(v_p_4910_);
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_p_4910_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v___x_4926_);
lean_inc(v_generation_4909_);
lean_inc_ref(v_lhs_4911_);
v___x_4927_ = lean_grind_internalize(v_lhs_4911_, v_generation_4909_, v___x_4926_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref_known(v___x_4927_, 1);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_rhs_4912_);
v___x_4928_ = lean_grind_internalize(v_rhs_4912_, v_generation_4909_, v___x_4926_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_dec_ref_known(v___x_4928_, 1);
v___x_4929_ = lean_box(0);
v___x_4930_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4910_, v___x_4929_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v___x_4931_; 
lean_dec_ref_known(v___x_4930_, 1);
v___x_4931_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4911_, v_rhs_4912_, v_proof_4908_, v_isHEq_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
return v___x_4931_;
}
else
{
lean_dec_ref(v_rhs_4912_);
lean_dec_ref(v_lhs_4911_);
lean_dec_ref(v_proof_4908_);
return v___x_4930_;
}
}
else
{
lean_dec_ref(v_rhs_4912_);
lean_dec_ref(v_lhs_4911_);
lean_dec_ref(v_p_4910_);
lean_dec_ref(v_proof_4908_);
return v___x_4928_;
}
}
else
{
lean_dec_ref_known(v___x_4926_, 1);
lean_dec_ref(v_rhs_4912_);
lean_dec_ref(v_lhs_4911_);
lean_dec_ref(v_p_4910_);
lean_dec(v_generation_4909_);
lean_dec_ref(v_proof_4908_);
return v___x_4927_;
}
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v_rhs_4912_);
lean_dec_ref(v_lhs_4911_);
v___x_4932_ = lean_box(0);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc_ref(v_a_4917_);
lean_inc(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_p_4910_);
v___x_4933_ = lean_grind_internalize(v_p_4910_, v_generation_4909_, v___x_4932_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v___x_4934_; 
lean_dec_ref_known(v___x_4933_, 1);
v___x_4934_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4919_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4936_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4934_, 1);
v___x_4936_ = l_Lean_Meta_mkEqFalse(v_proof_4908_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4938_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4910_, v_a_4935_, v_a_4937_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
return v___x_4938_;
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
lean_dec(v_a_4935_);
lean_dec_ref(v_p_4910_);
v_a_4939_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v___x_4936_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4936_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec_ref(v_p_4910_);
lean_dec_ref(v_proof_4908_);
v_a_4947_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4934_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4934_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
else
{
lean_dec_ref(v_p_4910_);
lean_dec_ref(v_proof_4908_);
return v___x_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4955_ = _args[0];
lean_object* v_generation_4956_ = _args[1];
lean_object* v_p_4957_ = _args[2];
lean_object* v_lhs_4958_ = _args[3];
lean_object* v_rhs_4959_ = _args[4];
lean_object* v_isNeg_4960_ = _args[5];
lean_object* v_isHEq_4961_ = _args[6];
lean_object* v_a_4962_ = _args[7];
lean_object* v_a_4963_ = _args[8];
lean_object* v_a_4964_ = _args[9];
lean_object* v_a_4965_ = _args[10];
lean_object* v_a_4966_ = _args[11];
lean_object* v_a_4967_ = _args[12];
lean_object* v_a_4968_ = _args[13];
lean_object* v_a_4969_ = _args[14];
lean_object* v_a_4970_ = _args[15];
lean_object* v_a_4971_ = _args[16];
lean_object* v_a_4972_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4973_; uint8_t v_isHEq_boxed_4974_; lean_object* v_res_4975_; 
v_isNeg_boxed_4973_ = lean_unbox(v_isNeg_4960_);
v_isHEq_boxed_4974_ = lean_unbox(v_isHEq_4961_);
v_res_4975_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4955_, v_generation_4956_, v_p_4957_, v_lhs_4958_, v_rhs_4959_, v_isNeg_boxed_4973_, v_isHEq_boxed_4974_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
lean_dec(v_a_4971_);
lean_dec_ref(v_a_4970_);
lean_dec(v_a_4969_);
lean_dec_ref(v_a_4968_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec(v_a_4962_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4979_, lean_object* v_generation_4980_, lean_object* v_p_4981_, uint8_t v_isNeg_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v___x_4994_; 
lean_inc_ref(v_p_4981_);
v___x_4994_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4981_, v_a_4990_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref_known(v___x_4994_, 1);
v___x_4996_ = l_Lean_Expr_cleanupAnnotations(v_a_4995_);
v___x_4997_ = l_Lean_Expr_isApp(v___x_4996_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec_ref(v___x_4996_);
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_4998_;
}
else
{
lean_object* v_arg_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
v_arg_4999_ = lean_ctor_get(v___x_4996_, 1);
lean_inc_ref(v_arg_4999_);
v___x_5000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4996_);
v___x_5001_ = l_Lean_Expr_isApp(v___x_5000_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; 
lean_dec_ref(v___x_5000_);
lean_dec_ref(v_arg_4999_);
v___x_5002_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5002_;
}
else
{
lean_object* v_arg_5003_; lean_object* v___x_5004_; uint8_t v___x_5005_; 
v_arg_5003_ = lean_ctor_get(v___x_5000_, 1);
lean_inc_ref(v_arg_5003_);
v___x_5004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5000_);
v___x_5005_ = l_Lean_Expr_isApp(v___x_5004_);
if (v___x_5005_ == 0)
{
lean_object* v___x_5006_; 
lean_dec_ref(v___x_5004_);
lean_dec_ref(v_arg_5003_);
lean_dec_ref(v_arg_4999_);
v___x_5006_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5006_;
}
else
{
lean_object* v_arg_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; uint8_t v___x_5010_; 
v_arg_5007_ = lean_ctor_get(v___x_5004_, 1);
lean_inc_ref(v_arg_5007_);
v___x_5008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5004_);
v___x_5009_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5010_ = l_Lean_Expr_isConstOf(v___x_5008_, v___x_5009_);
if (v___x_5010_ == 0)
{
uint8_t v___x_5011_; 
lean_dec_ref(v_arg_5003_);
v___x_5011_ = l_Lean_Expr_isApp(v___x_5008_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref(v___x_5008_);
lean_dec_ref(v_arg_5007_);
lean_dec_ref(v_arg_4999_);
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5012_;
}
else
{
lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5008_);
v___x_5014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5015_ = l_Lean_Expr_isConstOf(v___x_5013_, v___x_5014_);
lean_dec_ref(v___x_5013_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; 
lean_dec_ref(v_arg_5007_);
lean_dec_ref(v_arg_4999_);
v___x_5016_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5016_;
}
else
{
lean_object* v___x_5017_; 
v___x_5017_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4979_, v_generation_4980_, v_p_4981_, v_arg_5007_, v_arg_4999_, v_isNeg_4982_, v___x_5015_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5017_;
}
}
}
else
{
uint8_t v___x_5018_; 
lean_dec_ref(v___x_5008_);
v___x_5018_ = l_Lean_Expr_isProp(v_arg_5007_);
lean_dec_ref(v_arg_5007_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
v___x_5019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4979_, v_generation_4980_, v_p_4981_, v_arg_5003_, v_arg_4999_, v_isNeg_4982_, v___x_5018_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5019_;
}
else
{
lean_object* v___x_5020_; 
lean_dec_ref(v_arg_5003_);
lean_dec_ref(v_arg_4999_);
v___x_5020_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4979_, v_generation_4980_, v_p_4981_, v_isNeg_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_5020_;
}
}
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec_ref(v_p_4981_);
lean_dec(v_generation_4980_);
lean_dec_ref(v_proof_4979_);
v_a_5021_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4994_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4994_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5029_, lean_object* v_generation_5030_, lean_object* v_p_5031_, lean_object* v_isNeg_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
uint8_t v_isNeg_boxed_5044_; lean_object* v_res_5045_; 
v_isNeg_boxed_5044_ = lean_unbox(v_isNeg_5032_);
v_res_5045_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5029_, v_generation_5030_, v_p_5031_, v_isNeg_boxed_5044_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
lean_dec(v_a_5033_);
return v_res_5045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5054_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5055_ = l_Lean_Name_append(v___x_5054_, v___x_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5056_, lean_object* v_proof_5057_, lean_object* v_generation_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___x_5101_; lean_object* v_toCold_5102_; lean_object* v_options_5103_; uint8_t v_hasTrace_5104_; 
lean_inc_ref(v_fact_5056_);
v___x_5101_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5056_, v_a_5059_);
lean_dec_ref(v___x_5101_);
v_toCold_5102_ = lean_ctor_get(v_a_5067_, 0);
v_options_5103_ = lean_ctor_get(v_toCold_5102_, 2);
v_hasTrace_5104_ = lean_ctor_get_uint8(v_options_5103_, sizeof(void*)*1);
if (v_hasTrace_5104_ == 0)
{
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
goto v___jp_5083_;
}
else
{
lean_object* v_inheritedTraceOptions_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
v_inheritedTraceOptions_5105_ = lean_ctor_get(v_toCold_5102_, 11);
v___x_5106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5108_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5105_, v_options_5103_, v___x_5107_);
if (v___x_5108_ == 0)
{
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
goto v___jp_5083_;
}
else
{
lean_object* v___x_5109_; 
v___x_5109_ = l_Lean_Meta_Grind_updateLastTag(v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
lean_dec_ref_known(v___x_5109_, 1);
lean_inc_ref(v_fact_5056_);
v___x_5110_ = l_Lean_MessageData_ofExpr(v_fact_5056_);
v___x_5111_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5106_, v___x_5110_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_dec_ref_known(v___x_5111_, 1);
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
goto v___jp_5083_;
}
else
{
lean_dec(v_generation_5058_);
lean_dec_ref(v_proof_5057_);
lean_dec_ref(v_fact_5056_);
return v___x_5111_;
}
}
else
{
lean_dec(v_generation_5058_);
lean_dec_ref(v_proof_5057_);
lean_dec_ref(v_fact_5056_);
return v___x_5109_;
}
}
}
v___jp_5070_:
{
uint8_t v___x_5081_; lean_object* v___x_5082_; 
v___x_5081_ = 0;
v___x_5082_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5057_, v_generation_5058_, v_fact_5056_, v___x_5081_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
return v___x_5082_;
}
v___jp_5083_:
{
lean_object* v___x_5094_; uint8_t v___x_5095_; 
lean_inc_ref(v_fact_5056_);
v___x_5094_ = l_Lean_Expr_cleanupAnnotations(v_fact_5056_);
v___x_5095_ = l_Lean_Expr_isApp(v___x_5094_);
if (v___x_5095_ == 0)
{
lean_dec_ref(v___x_5094_);
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5088_;
v___y_5076_ = v___y_5089_;
v___y_5077_ = v___y_5090_;
v___y_5078_ = v___y_5091_;
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
goto v___jp_5070_;
}
else
{
lean_object* v_arg_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; 
v_arg_5096_ = lean_ctor_get(v___x_5094_, 1);
lean_inc_ref(v_arg_5096_);
v___x_5097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5094_);
v___x_5098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5099_ = l_Lean_Expr_isConstOf(v___x_5097_, v___x_5098_);
lean_dec_ref(v___x_5097_);
if (v___x_5099_ == 0)
{
lean_dec_ref(v_arg_5096_);
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5088_;
v___y_5076_ = v___y_5089_;
v___y_5077_ = v___y_5090_;
v___y_5078_ = v___y_5091_;
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
goto v___jp_5070_;
}
else
{
lean_object* v___x_5100_; 
lean_dec_ref(v_fact_5056_);
v___x_5100_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5057_, v_generation_5058_, v_arg_5096_, v___x_5099_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
return v___x_5100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5112_, lean_object* v_proof_5113_, lean_object* v_generation_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5112_, v_proof_5113_, v_generation_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_);
lean_dec(v_a_5124_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
lean_dec(v_a_5118_);
lean_dec_ref(v_a_5117_);
lean_dec(v_a_5116_);
lean_dec(v_a_5115_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5130_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; uint8_t v___x_5143_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
lean_dec_ref_known(v___x_5141_, 1);
v___x_5143_ = lean_unbox(v_a_5142_);
lean_dec(v_a_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5144_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5145_ = l_Lean_Core_checkSystem(v___x_5144_, v___y_5138_, v___y_5139_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v___x_5146_; 
lean_dec_ref_known(v___x_5145_, 1);
v___x_5146_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5130_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5220_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5149_ = v___x_5146_;
v_isShared_5150_ = v_isSharedCheck_5220_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5146_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5220_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
if (lean_obj_tag(v_a_5147_) == 1)
{
lean_object* v_val_5151_; 
lean_del_object(v___x_5149_);
v_val_5151_ = lean_ctor_get(v_a_5147_, 0);
lean_inc(v_val_5151_);
lean_dec_ref_known(v_a_5147_, 1);
switch(lean_obj_tag(v_val_5151_))
{
case 0:
{
lean_object* v_lhs_5152_; lean_object* v_rhs_5153_; lean_object* v_proof_5154_; uint8_t v_isHEq_5155_; lean_object* v___x_5156_; 
v_lhs_5152_ = lean_ctor_get(v_val_5151_, 0);
lean_inc_ref(v_lhs_5152_);
v_rhs_5153_ = lean_ctor_get(v_val_5151_, 1);
lean_inc_ref(v_rhs_5153_);
v_proof_5154_ = lean_ctor_get(v_val_5151_, 2);
lean_inc_ref(v_proof_5154_);
v_isHEq_5155_ = lean_ctor_get_uint8(v_val_5151_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5151_, 3);
v___x_5156_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5152_, v_rhs_5153_, v_proof_5154_, v_isHEq_5155_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_dec_ref_known(v___x_5156_, 1);
goto _start;
}
else
{
lean_object* v_a_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5165_; 
v_a_5158_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_5160_ = v___x_5156_;
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_a_5158_);
lean_dec(v___x_5156_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5163_; 
if (v_isShared_5161_ == 0)
{
v___x_5163_ = v___x_5160_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5158_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
}
}
case 1:
{
lean_object* v_prop_5166_; lean_object* v_proof_5167_; lean_object* v_generation_5168_; lean_object* v___x_5169_; 
v_prop_5166_ = lean_ctor_get(v_val_5151_, 0);
lean_inc_ref(v_prop_5166_);
v_proof_5167_ = lean_ctor_get(v_val_5151_, 1);
lean_inc_ref(v_proof_5167_);
v_generation_5168_ = lean_ctor_get(v_val_5151_, 2);
lean_inc(v_generation_5168_);
lean_dec_ref_known(v_val_5151_, 3);
v___x_5169_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5166_, v_proof_5167_, v_generation_5168_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_dec_ref_known(v___x_5169_, 1);
goto _start;
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
v_a_5171_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5169_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5169_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
case 2:
{
lean_object* v_e_5179_; lean_object* v___x_5180_; 
v_e_5179_ = lean_ctor_get(v_val_5151_, 0);
lean_inc_ref(v_e_5179_);
lean_dec_ref_known(v_val_5151_, 1);
v___x_5180_ = l_Lean_Meta_Grind_propagateUp(v_e_5179_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_dec_ref_known(v___x_5180_, 1);
goto _start;
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
v_a_5182_ = lean_ctor_get(v___x_5180_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5180_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5180_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
case 3:
{
lean_object* v_solverId_5190_; lean_object* v_lhs_5191_; lean_object* v_rhs_5192_; lean_object* v___x_5193_; 
v_solverId_5190_ = lean_ctor_get(v_val_5151_, 0);
lean_inc(v_solverId_5190_);
v_lhs_5191_ = lean_ctor_get(v_val_5151_, 1);
lean_inc_ref(v_lhs_5191_);
v_rhs_5192_ = lean_ctor_get(v_val_5151_, 2);
lean_inc_ref(v_rhs_5192_);
lean_dec_ref_known(v_val_5151_, 3);
v___x_5193_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5190_, v_lhs_5191_, v_rhs_5192_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
lean_dec(v_solverId_5190_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_dec_ref_known(v___x_5193_, 1);
goto _start;
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
v_a_5195_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5193_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5193_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
default: 
{
lean_object* v_solverId_5203_; lean_object* v_lhs_5204_; lean_object* v_rhs_5205_; lean_object* v___x_5206_; 
v_solverId_5203_ = lean_ctor_get(v_val_5151_, 0);
lean_inc(v_solverId_5203_);
v_lhs_5204_ = lean_ctor_get(v_val_5151_, 1);
lean_inc_ref(v_lhs_5204_);
v_rhs_5205_ = lean_ctor_get(v_val_5151_, 2);
lean_inc_ref(v_rhs_5205_);
lean_dec_ref_known(v_val_5151_, 3);
v___x_5206_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5203_, v_lhs_5204_, v_rhs_5205_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
lean_dec(v_solverId_5203_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_dec_ref_known(v___x_5206_, 1);
goto _start;
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
v_a_5208_ = lean_ctor_get(v___x_5206_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5206_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5206_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5206_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
}
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5218_; 
lean_dec(v_a_5147_);
v___x_5216_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5216_);
v___x_5218_ = v___x_5149_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5216_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
v_a_5221_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5146_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5146_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5236_; 
v_a_5229_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5145_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5145_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5234_; 
if (v_isShared_5232_ == 0)
{
v___x_5234_ = v___x_5231_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
else
{
lean_object* v___x_5237_; 
v___x_5237_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5130_);
if (lean_obj_tag(v___x_5237_) == 0)
{
lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5245_; 
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5245_ == 0)
{
lean_object* v_unused_5246_; 
v_unused_5246_ = lean_ctor_get(v___x_5237_, 0);
lean_dec(v_unused_5246_);
v___x_5239_ = v___x_5237_;
v_isShared_5240_ = v_isSharedCheck_5245_;
goto v_resetjp_5238_;
}
else
{
lean_dec(v___x_5237_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5245_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5241_; lean_object* v___x_5243_; 
v___x_5241_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 0, v___x_5241_);
v___x_5243_ = v___x_5239_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
v_a_5247_ = lean_ctor_get(v___x_5237_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5237_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5237_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5237_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
v_a_5255_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5141_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5141_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v___y_5264_);
lean_dec(v___y_5263_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5286_ = lean_box(0);
v___x_5287_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
lean_dec(v_a_5278_);
lean_dec_ref(v_a_5277_);
lean_dec(v_a_5276_);
lean_dec(v_a_5275_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5300_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5300_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5300_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v_fst_5292_; 
v_fst_5292_ = lean_ctor_get(v_a_5288_, 0);
lean_inc(v_fst_5292_);
lean_dec(v_a_5288_);
if (lean_obj_tag(v_fst_5292_) == 0)
{
lean_object* v___x_5294_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5286_);
v___x_5294_ = v___x_5290_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5286_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
else
{
lean_object* v_val_5296_; lean_object* v___x_5298_; 
v_val_5296_ = lean_ctor_get(v_fst_5292_, 0);
lean_inc(v_val_5296_);
lean_dec_ref_known(v_fst_5292_, 1);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v_val_5296_);
v___x_5298_ = v___x_5290_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_val_5296_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
v_a_5301_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5287_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5287_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = lean_grind_process_to_do(v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5321_, lean_object* v_a_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5335_, lean_object* v_a_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5335_, v_a_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v_a_5336_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5349_, lean_object* v_proof_5350_, lean_object* v_generation_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
uint8_t v___x_5363_; 
lean_inc_ref(v_fact_5349_);
v___x_5363_ = l_Lean_Expr_isTrue(v_fact_5349_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
v___x_5364_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5352_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5395_; 
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5367_ = v___x_5364_;
v_isShared_5368_ = v_isSharedCheck_5395_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5364_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5395_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
uint8_t v___x_5369_; 
v___x_5369_ = lean_unbox(v_a_5365_);
lean_dec(v_a_5365_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; 
lean_del_object(v___x_5367_);
lean_inc(v_a_5361_);
lean_inc_ref(v_a_5360_);
lean_inc(v_a_5359_);
lean_inc_ref(v_a_5358_);
lean_inc(v_a_5357_);
lean_inc_ref(v_a_5356_);
lean_inc(v_a_5355_);
lean_inc_ref(v_a_5354_);
lean_inc(v_a_5353_);
lean_inc(v_a_5352_);
v___x_5370_ = lean_grind_process_to_do(v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v___x_5371_; 
lean_dec_ref_known(v___x_5370_, 1);
v___x_5371_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5352_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5382_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5374_ = v___x_5371_;
v_isShared_5375_ = v_isSharedCheck_5382_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_a_5372_);
lean_dec(v___x_5371_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5382_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
uint8_t v___x_5376_; 
v___x_5376_ = lean_unbox(v_a_5372_);
lean_dec(v_a_5372_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; 
lean_del_object(v___x_5374_);
v___x_5377_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5349_, v_proof_5350_, v_generation_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
return v___x_5377_;
}
else
{
lean_object* v___x_5378_; lean_object* v___x_5380_; 
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
v___x_5378_ = lean_box(0);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v___x_5378_);
v___x_5380_ = v___x_5374_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5378_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
v_a_5383_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5371_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5371_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
else
{
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
return v___x_5370_;
}
}
else
{
lean_object* v___x_5391_; lean_object* v___x_5393_; 
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
v___x_5391_ = lean_box(0);
if (v_isShared_5368_ == 0)
{
lean_ctor_set(v___x_5367_, 0, v___x_5391_);
v___x_5393_ = v___x_5367_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5391_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
v_a_5396_ = lean_ctor_get(v___x_5364_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5364_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5364_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5364_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
else
{
lean_object* v___x_5404_; lean_object* v___x_5405_; 
lean_dec(v_generation_5351_);
lean_dec_ref(v_proof_5350_);
lean_dec_ref(v_fact_5349_);
v___x_5404_ = lean_box(0);
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5404_);
return v___x_5405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5406_, lean_object* v_proof_5407_, lean_object* v_generation_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_Lean_Meta_Grind_add(v_fact_5406_, v_proof_5407_, v_generation_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
lean_dec(v_a_5412_);
lean_dec_ref(v_a_5411_);
lean_dec(v_a_5410_);
lean_dec(v_a_5409_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5421_, lean_object* v_generation_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_){
_start:
{
lean_object* v___x_5434_; 
lean_inc(v_fvarId_5421_);
v___x_5434_ = l_Lean_FVarId_getType___redArg(v_fvarId_5421_, v_a_5429_, v_a_5431_, v_a_5432_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 0);
lean_inc(v_a_5435_);
lean_dec_ref_known(v___x_5434_, 1);
v___x_5436_ = l_Lean_mkFVar(v_fvarId_5421_);
v___x_5437_ = l_Lean_Meta_Grind_add(v_a_5435_, v___x_5436_, v_generation_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
return v___x_5437_;
}
else
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5445_; 
lean_dec(v_generation_5422_);
lean_dec(v_fvarId_5421_);
v_a_5438_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5440_ = v___x_5434_;
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5434_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v___x_5443_; 
if (v_isShared_5441_ == 0)
{
v___x_5443_ = v___x_5440_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5446_, lean_object* v_generation_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5446_, v_generation_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_);
lean_dec(v_a_5457_);
lean_dec_ref(v_a_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v_a_5452_);
lean_dec(v_a_5451_);
lean_dec_ref(v_a_5450_);
lean_dec(v_a_5449_);
lean_dec(v_a_5448_);
return v_res_5459_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
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
