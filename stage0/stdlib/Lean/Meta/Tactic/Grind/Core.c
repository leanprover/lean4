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
uint8_t l_Lean_Expr_isArrow(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
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
uint8_t v___y_154_; uint8_t v___x_156_; 
v___x_156_ = l_Lean_Expr_isApp(v_parent_152_);
if (v___x_156_ == 0)
{
v___y_154_ = v___x_156_;
goto v___jp_153_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_Meta_Grind_isMatchCond(v_parent_152_);
if (v___x_157_ == 0)
{
v___y_154_ = v___x_156_;
goto v___jp_153_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = l_Lean_Expr_isArrow(v_parent_152_);
return v___x_158_;
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Expr_isArrow(v_parent_152_);
return v___x_155_;
}
else
{
return v___y_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_159_);
lean_dec_ref(v_parent_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object* v_msgData_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; lean_object* v_env_169_; uint8_t v___x_170_; lean_object* v_env_171_; lean_object* v___x_172_; lean_object* v_toCold_173_; lean_object* v_mctx_174_; lean_object* v_lctx_175_; lean_object* v_options_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_168_ = lean_st_ref_get(v___y_166_);
v_env_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_ref(v_env_169_);
lean_dec(v___x_168_);
v___x_170_ = 0;
v_env_171_ = l_Lean_Environment_setRecordingDeps(v_env_169_, v___x_170_);
v___x_172_ = lean_st_ref_get(v___y_164_);
v_toCold_173_ = lean_ctor_get(v___y_165_, 0);
v_mctx_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc_ref(v_mctx_174_);
lean_dec(v___x_172_);
v_lctx_175_ = lean_ctor_get(v___y_163_, 2);
v_options_176_ = lean_ctor_get(v_toCold_173_, 2);
lean_inc_ref(v_options_176_);
lean_inc_ref(v_lctx_175_);
v___x_177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_177_, 0, v_env_171_);
lean_ctor_set(v___x_177_, 1, v_mctx_174_);
lean_ctor_set(v___x_177_, 2, v_lctx_175_);
lean_ctor_set(v___x_177_, 3, v_options_176_);
v___x_178_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_msgData_162_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_186_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_187_; double v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_float_of_nat(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_192_, lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_246_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 2);
v___x_200_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_246_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_246_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_traceState_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_cache_211_; lean_object* v_recordedDeps_212_; lean_object* v_messages_213_; lean_object* v_infoState_214_; lean_object* v_snapshotTasks_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
v___x_205_ = lean_st_ref_take(v___y_197_);
v_traceState_206_ = lean_ctor_get(v___x_205_, 4);
v_env_207_ = lean_ctor_get(v___x_205_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_205_, 1);
v_ngen_209_ = lean_ctor_get(v___x_205_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_205_, 3);
v_cache_211_ = lean_ctor_get(v___x_205_, 5);
v_recordedDeps_212_ = lean_ctor_get(v___x_205_, 6);
v_messages_213_ = lean_ctor_get(v___x_205_, 7);
v_infoState_214_ = lean_ctor_get(v___x_205_, 8);
v_snapshotTasks_215_ = lean_ctor_get(v___x_205_, 9);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v___x_205_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snapshotTasks_215_);
lean_inc(v_infoState_214_);
lean_inc(v_messages_213_);
lean_inc(v_recordedDeps_212_);
lean_inc(v_cache_211_);
lean_inc(v_traceState_206_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_205_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint64_t v_tid_219_; lean_object* v_traces_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_tid_219_ = lean_ctor_get_uint64(v_traceState_206_, sizeof(void*)*1);
v_traces_220_ = lean_ctor_get(v_traceState_206_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_traceState_206_);
if (v_isSharedCheck_244_ == 0)
{
v___x_222_ = v_traceState_206_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_traces_220_);
lean_dec(v_traceState_206_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; double v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_224_ = lean_box(0);
v___x_225_ = lean_box(0);
v___x_226_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_227_ = 0;
v___x_228_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_229_, 0, v_cls_192_);
lean_ctor_set(v___x_229_, 1, v___x_225_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_ctor_set_float(v___x_229_, sizeof(void*)*3, v___x_226_);
lean_ctor_set_float(v___x_229_, sizeof(void*)*3 + 8, v___x_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3 + 16, v___x_227_);
v___x_230_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_231_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v_a_201_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_inc(v_ref_199_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_ref_199_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_PersistentArray_push___redArg(v_traces_220_, v___x_232_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_233_);
v___x_235_ = v___x_222_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_233_);
lean_ctor_set_uint64(v_reuseFailAlloc_243_, sizeof(void*)*1, v_tid_219_);
v___x_235_ = v_reuseFailAlloc_243_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 4, v___x_235_);
v___x_237_ = v___x_217_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_env_207_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_cache_211_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_recordedDeps_212_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_messages_213_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v_infoState_214_);
lean_ctor_set(v_reuseFailAlloc_242_, 9, v_snapshotTasks_215_);
v___x_237_ = v_reuseFailAlloc_242_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_st_ref_put(v___y_197_, v___x_237_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_224_);
v___x_240_ = v___x_203_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_224_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_247_, v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_255_, lean_object* v_xs_256_, lean_object* v_v_257_, lean_object* v_i_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_xs_256_);
v___x_260_ = lean_nat_dec_lt(v_i_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v_i_258_);
lean_dec_ref(v_v_257_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_array_fget_borrowed(v_xs_256_, v_i_258_);
lean_inc_ref(v_v_257_);
lean_inc(v___x_262_);
v___x_263_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_255_, v___x_262_, v_v_257_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_i_258_, v___x_264_);
lean_dec(v_i_258_);
v_i_258_ = v___x_265_;
goto _start;
}
else
{
lean_object* v___x_267_; 
lean_dec_ref(v_v_257_);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v_i_258_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_268_, lean_object* v_xs_269_, lean_object* v_v_270_, lean_object* v_i_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_268_, v_xs_269_, v_v_270_, v_i_271_);
lean_dec_ref(v_xs_269_);
lean_dec_ref(v___x_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_273_, lean_object* v_xs_274_, lean_object* v_v_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_273_, v_xs_274_, v_v_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_278_, lean_object* v_xs_279_, lean_object* v_v_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_278_, v_xs_279_, v_v_280_);
lean_dec_ref(v_xs_279_);
lean_dec_ref(v___x_278_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_282_, lean_object* v_x_283_, size_t v_x_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_es_286_; lean_object* v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_j_290_; lean_object* v_entry_291_; 
v_es_286_ = lean_ctor_get(v_x_283_, 0);
v___x_287_ = lean_box(2);
v___x_288_ = ((size_t)31ULL);
v___x_289_ = lean_usize_land(v_x_284_, v___x_288_);
v_j_290_ = lean_usize_to_nat(v___x_289_);
v_entry_291_ = lean_array_get(v___x_287_, v_es_286_, v_j_290_);
switch(lean_obj_tag(v_entry_291_))
{
case 0:
{
lean_object* v_key_292_; uint8_t v___x_293_; 
v_key_292_ = lean_ctor_get(v_entry_291_, 0);
lean_inc(v_key_292_);
lean_dec_ref_known(v_entry_291_, 2);
v___x_293_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_282_, v_x_285_, v_key_292_);
if (v___x_293_ == 0)
{
lean_dec(v_j_290_);
return v_x_283_;
}
else
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
lean_inc_ref(v_es_286_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_x_283_, 0);
lean_dec(v_unused_302_);
v___x_295_ = v_x_283_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_x_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_array_set(v_es_286_, v_j_290_, v___x_287_);
lean_dec(v_j_290_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
case 1:
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_337_; 
lean_inc_ref(v_es_286_);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_x_283_, 0);
lean_dec(v_unused_338_);
v___x_304_ = v_x_283_;
v_isShared_305_ = v_isSharedCheck_337_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_x_283_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_337_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_node_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_336_; 
v_node_306_ = lean_ctor_get(v_entry_291_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_entry_291_);
if (v_isSharedCheck_336_ == 0)
{
v___x_308_ = v_entry_291_;
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_node_306_);
lean_dec(v_entry_291_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
size_t v___x_310_; lean_object* v_entries_311_; size_t v___x_312_; lean_object* v_newNode_313_; lean_object* v___x_314_; 
v___x_310_ = ((size_t)5ULL);
v_entries_311_ = lean_array_set(v_es_286_, v_j_290_, v___x_287_);
v___x_312_ = lean_usize_shift_right(v_x_284_, v___x_310_);
v_newNode_313_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_282_, v_node_306_, v___x_312_, v_x_285_);
lean_inc_ref(v_newNode_313_);
v___x_314_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_316_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_newNode_313_);
v___x_316_ = v___x_308_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_newNode_313_);
v___x_316_ = v_reuseFailAlloc_321_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_array_set(v_entries_311_, v_j_290_, v___x_316_);
lean_dec(v_j_290_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_317_);
v___x_319_ = v___x_304_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_val_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_newNode_313_);
lean_del_object(v___x_308_);
v_val_322_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v___x_314_, 1);
v_fst_323_ = lean_ctor_get(v_val_322_, 0);
v_snd_324_ = lean_ctor_get(v_val_322_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_val_322_);
if (v_isSharedCheck_335_ == 0)
{
v___x_326_ = v_val_322_;
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snd_324_);
lean_inc(v_fst_323_);
lean_dec(v_val_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_335_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_fst_323_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_snd_324_);
v___x_329_ = v_reuseFailAlloc_334_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_array_set(v_entries_311_, v_j_290_, v___x_329_);
lean_dec(v_j_290_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_330_);
v___x_332_ = v___x_304_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_290_);
lean_dec_ref(v_x_285_);
return v_x_283_;
}
}
}
else
{
lean_object* v_ks_339_; lean_object* v_vs_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_354_; 
v_ks_339_ = lean_ctor_get(v_x_283_, 0);
v_vs_340_ = lean_ctor_get(v_x_283_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_354_ == 0)
{
v___x_342_ = v_x_283_;
v_isShared_343_ = v_isSharedCheck_354_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_vs_340_);
lean_inc(v_ks_339_);
lean_dec(v_x_283_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_354_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; 
v___x_344_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_282_, v_ks_339_, v_x_285_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_346_; 
if (v_isShared_343_ == 0)
{
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_ks_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_vs_340_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
else
{
lean_object* v_val_348_; lean_object* v_keys_x27_349_; lean_object* v_vals_x27_350_; lean_object* v___x_352_; 
v_val_348_ = lean_ctor_get(v___x_344_, 0);
lean_inc_n(v_val_348_, 2);
lean_dec_ref_known(v___x_344_, 1);
v_keys_x27_349_ = l_Array_eraseIdx___redArg(v_ks_339_, v_val_348_);
v_vals_x27_350_ = l_Array_eraseIdx___redArg(v_vs_340_, v_val_348_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_vals_x27_350_);
lean_ctor_set(v___x_342_, 0, v_keys_x27_349_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_keys_x27_349_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_vals_x27_350_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_355_, lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
size_t v_x_22728__boxed_359_; lean_object* v_res_360_; 
v_x_22728__boxed_359_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_360_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_355_, v_x_356_, v_x_22728__boxed_359_, v_x_358_);
lean_dec_ref(v___x_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint64_t v___x_364_; size_t v_h_365_; lean_object* v___x_366_; 
lean_inc_ref(v_x_363_);
v___x_364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_361_, v_x_363_);
v_h_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_361_, v_x_362_, v_h_365_, v_x_363_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_367_, v_x_368_, v_x_369_);
lean_dec_ref(v___x_367_);
return v_res_370_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_383_ = l_Lean_Name_append(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
if (lean_obj_tag(v_as_x27_387_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_388_);
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v___x_403_; lean_object* v___y_405_; uint8_t v_a_446_; uint8_t v___x_460_; 
v_head_401_ = lean_ctor_get(v_as_x27_387_, 0);
v_tail_402_ = lean_ctor_get(v_as_x27_387_, 1);
v___x_403_ = lean_box(0);
v___x_460_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_401_);
if (v___x_460_ == 0)
{
v_a_446_ = v___x_460_;
goto v___jp_445_;
}
else
{
lean_object* v___x_461_; 
lean_inc(v_head_401_);
v___x_461_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_401_, v___y_389_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; uint8_t v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = lean_unbox(v_a_462_);
lean_dec(v_a_462_);
v_a_446_ = v___x_463_;
goto v___jp_445_;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_a_464_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_461_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_461_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v_toGoalState_407_; lean_object* v_mvarId_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_444_; 
v___x_406_ = lean_st_ref_take(v___y_405_);
v_toGoalState_407_ = lean_ctor_get(v___x_406_, 0);
v_mvarId_408_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_444_ == 0)
{
v___x_410_ = v___x_406_;
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_mvarId_408_);
lean_inc(v_toGoalState_407_);
lean_dec(v___x_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_444_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_nextDeclIdx_412_; lean_object* v_enodeMap_413_; lean_object* v_exprs_414_; lean_object* v_parents_415_; lean_object* v_congrTable_416_; lean_object* v_appMap_417_; lean_object* v_indicesFound_418_; lean_object* v_toProcess_419_; lean_object* v_internalizing_420_; uint8_t v_inconsistent_421_; lean_object* v_nextIdx_422_; lean_object* v_newRawFacts_423_; lean_object* v_facts_424_; lean_object* v_extThms_425_; lean_object* v_ematch_426_; lean_object* v_inj_427_; lean_object* v_split_428_; lean_object* v_clean_429_; lean_object* v_sstates_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_443_; 
v_nextDeclIdx_412_ = lean_ctor_get(v_toGoalState_407_, 0);
v_enodeMap_413_ = lean_ctor_get(v_toGoalState_407_, 1);
v_exprs_414_ = lean_ctor_get(v_toGoalState_407_, 2);
v_parents_415_ = lean_ctor_get(v_toGoalState_407_, 3);
v_congrTable_416_ = lean_ctor_get(v_toGoalState_407_, 4);
v_appMap_417_ = lean_ctor_get(v_toGoalState_407_, 5);
v_indicesFound_418_ = lean_ctor_get(v_toGoalState_407_, 6);
v_toProcess_419_ = lean_ctor_get(v_toGoalState_407_, 7);
v_internalizing_420_ = lean_ctor_get(v_toGoalState_407_, 8);
v_inconsistent_421_ = lean_ctor_get_uint8(v_toGoalState_407_, sizeof(void*)*18);
v_nextIdx_422_ = lean_ctor_get(v_toGoalState_407_, 9);
v_newRawFacts_423_ = lean_ctor_get(v_toGoalState_407_, 10);
v_facts_424_ = lean_ctor_get(v_toGoalState_407_, 11);
v_extThms_425_ = lean_ctor_get(v_toGoalState_407_, 12);
v_ematch_426_ = lean_ctor_get(v_toGoalState_407_, 13);
v_inj_427_ = lean_ctor_get(v_toGoalState_407_, 14);
v_split_428_ = lean_ctor_get(v_toGoalState_407_, 15);
v_clean_429_ = lean_ctor_get(v_toGoalState_407_, 16);
v_sstates_430_ = lean_ctor_get(v_toGoalState_407_, 17);
v_isSharedCheck_443_ = !lean_is_exclusive(v_toGoalState_407_);
if (v_isSharedCheck_443_ == 0)
{
v___x_432_ = v_toGoalState_407_;
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_sstates_430_);
lean_inc(v_clean_429_);
lean_inc(v_split_428_);
lean_inc(v_inj_427_);
lean_inc(v_ematch_426_);
lean_inc(v_extThms_425_);
lean_inc(v_facts_424_);
lean_inc(v_newRawFacts_423_);
lean_inc(v_nextIdx_422_);
lean_inc(v_internalizing_420_);
lean_inc(v_toProcess_419_);
lean_inc(v_indicesFound_418_);
lean_inc(v_appMap_417_);
lean_inc(v_congrTable_416_);
lean_inc(v_parents_415_);
lean_inc(v_exprs_414_);
lean_inc(v_enodeMap_413_);
lean_inc(v_nextDeclIdx_412_);
lean_dec(v_toGoalState_407_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_443_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_inc(v_head_401_);
v___x_434_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_413_, v_congrTable_416_, v_head_401_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 4, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_nextDeclIdx_412_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_enodeMap_413_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_exprs_414_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_parents_415_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_442_, 5, v_appMap_417_);
lean_ctor_set(v_reuseFailAlloc_442_, 6, v_indicesFound_418_);
lean_ctor_set(v_reuseFailAlloc_442_, 7, v_toProcess_419_);
lean_ctor_set(v_reuseFailAlloc_442_, 8, v_internalizing_420_);
lean_ctor_set(v_reuseFailAlloc_442_, 9, v_nextIdx_422_);
lean_ctor_set(v_reuseFailAlloc_442_, 10, v_newRawFacts_423_);
lean_ctor_set(v_reuseFailAlloc_442_, 11, v_facts_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 12, v_extThms_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 13, v_ematch_426_);
lean_ctor_set(v_reuseFailAlloc_442_, 14, v_inj_427_);
lean_ctor_set(v_reuseFailAlloc_442_, 15, v_split_428_);
lean_ctor_set(v_reuseFailAlloc_442_, 16, v_clean_429_);
lean_ctor_set(v_reuseFailAlloc_442_, 17, v_sstates_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_442_, sizeof(void*)*18, v_inconsistent_421_);
v___x_436_ = v_reuseFailAlloc_442_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_436_);
v___x_438_ = v___x_410_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_mvarId_408_);
v___x_438_ = v_reuseFailAlloc_441_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_st_ref_put(v___y_405_, v___x_438_);
v_as_x27_387_ = v_tail_402_;
v_b_388_ = v___x_403_;
goto _start;
}
}
}
}
}
v___jp_445_:
{
if (v_a_446_ == 0)
{
v_as_x27_387_ = v_tail_402_;
v_b_388_ = v___x_403_;
goto _start;
}
else
{
lean_object* v_toCold_448_; lean_object* v_options_449_; uint8_t v_hasTrace_450_; 
v_toCold_448_ = lean_ctor_get(v___y_397_, 0);
v_options_449_ = lean_ctor_get(v_toCold_448_, 2);
v_hasTrace_450_ = lean_ctor_get_uint8(v_options_449_, sizeof(void*)*1);
if (v_hasTrace_450_ == 0)
{
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
lean_object* v_inheritedTraceOptions_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_inheritedTraceOptions_451_ = lean_ctor_get(v_toCold_448_, 11);
v___x_452_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_453_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_451_, v_options_449_, v___x_453_);
if (v___x_454_ == 0)
{
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Grind_updateLastTag(v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref_known(v___x_455_, 1);
v___x_456_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_401_);
v___x_457_ = l_Lean_MessageData_ofExpr(v_head_401_);
v___x_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_452_, v___x_458_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_dec_ref_known(v___x_459_, 1);
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
return v___x_459_;
}
}
else
{
return v___x_455_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_472_, v_b_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v_as_x27_472_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_Grind_getParents___redArg(v_root_486_, v_a_487_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_499_);
v___x_501_ = lean_box(0);
v___x_502_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_500_, v___x_501_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v___x_500_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_502_, 0);
lean_dec(v_unused_510_);
v___x_504_ = v___x_502_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_dec(v___x_502_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v_a_499_);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_499_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_a_499_);
v_a_511_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_502_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_502_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_root_519_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_532_, lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_532_, v_x_534_, v_x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_537_, lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_537_, v_00_u03b2_538_, v_x_539_, v_x_540_);
lean_dec_ref(v___x_537_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_542_, v_msg_543_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_556_, v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec(v___y_558_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_570_, lean_object* v_as_x27_571_, lean_object* v_b_572_, lean_object* v_a_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_571_, v_b_572_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_586_, lean_object* v_as_x27_587_, lean_object* v_b_588_, lean_object* v_a_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_586_, v_as_x27_587_, v_b_588_, v_a_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
lean_dec(v_as_x27_587_);
lean_dec(v_as_586_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_602_, lean_object* v_00_u03b2_603_, lean_object* v_x_604_, size_t v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_602_, v_x_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_608_, lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_23190__boxed_613_; lean_object* v_res_614_; 
v_x_23190__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_614_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_608_, v_00_u03b2_609_, v_x_610_, v_x_23190__boxed_613_, v_x_612_);
lean_dec_ref(v___x_608_);
return v_res_614_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
if (lean_obj_tag(v_as_x27_618_) == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v_b_619_);
return v___x_631_;
}
else
{
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v_a_649_; uint8_t v___x_663_; 
v_head_632_ = lean_ctor_get(v_as_x27_618_, 0);
v_tail_633_ = lean_ctor_get(v_as_x27_618_, 1);
v___x_634_ = lean_box(0);
v___x_663_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_632_);
if (v___x_663_ == 0)
{
v_a_649_ = v___x_663_;
goto v___jp_648_;
}
else
{
lean_object* v___x_664_; 
lean_inc(v_head_632_);
v___x_664_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_632_, v___y_620_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; uint8_t v___x_666_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v_a_649_ = v___x_666_;
goto v___jp_648_;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_664_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_664_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
v___jp_635_:
{
lean_object* v___x_646_; 
lean_inc(v_head_632_);
v___x_646_ = l_Lean_Meta_Grind_addCongrTable(v_head_632_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
v_as_x27_618_ = v_tail_633_;
v_b_619_ = v___x_634_;
goto _start;
}
else
{
return v___x_646_;
}
}
v___jp_648_:
{
if (v_a_649_ == 0)
{
v_as_x27_618_ = v_tail_633_;
v_b_619_ = v___x_634_;
goto _start;
}
else
{
lean_object* v_toCold_651_; lean_object* v_options_652_; uint8_t v_hasTrace_653_; 
v_toCold_651_ = lean_ctor_get(v___y_628_, 0);
v_options_652_ = lean_ctor_get(v_toCold_651_, 2);
v_hasTrace_653_ = lean_ctor_get_uint8(v_options_652_, sizeof(void*)*1);
if (v_hasTrace_653_ == 0)
{
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
goto v___jp_635_;
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
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
goto v___jp_635_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Grind_updateLastTag(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec_ref_known(v___x_658_, 1);
v___x_659_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_632_);
v___x_660_ = l_Lean_MessageData_ofExpr(v_head_632_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_655_, v___x_661_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
goto v___jp_635_;
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_675_, lean_object* v_b_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_675_, v_b_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec(v___y_677_);
lean_dec(v_as_x27_675_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_689_);
v___x_702_ = lean_box(0);
v___x_703_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_701_, v___x_702_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v___x_701_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_711_);
v___x_705_ = v___x_703_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_703_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_702_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_702_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_parents_712_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_725_, lean_object* v_as_x27_726_, lean_object* v_b_727_, lean_object* v_a_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_726_, v_b_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_741_, lean_object* v_as_x27_742_, lean_object* v_b_743_, lean_object* v_a_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_741_, v_as_x27_742_, v_b_743_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v_as_x27_742_);
lean_dec(v_as_741_);
return v_res_756_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_757_, lean_object* v_i_758_, lean_object* v_k_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_keys_757_);
v___x_761_ = lean_nat_dec_lt(v_i_758_, v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v_i_758_);
return v___x_761_;
}
else
{
lean_object* v_k_x27_762_; uint8_t v___x_763_; 
v_k_x27_762_ = lean_array_fget_borrowed(v_keys_757_, v_i_758_);
v___x_763_ = l_Lean_instBEqMVarId_beq(v_k_759_, v_k_x27_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v_i_758_, v___x_764_);
lean_dec(v_i_758_);
v_i_758_ = v___x_765_;
goto _start;
}
else
{
lean_dec(v_i_758_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_767_, lean_object* v_i_768_, lean_object* v_k_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_767_, v_i_768_, v_k_769_);
lean_dec(v_k_769_);
lean_dec_ref(v_keys_767_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_772_, size_t v_x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v_es_775_; lean_object* v___x_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v_j_779_; lean_object* v___x_780_; 
v_es_775_ = lean_ctor_get(v_x_772_, 0);
v___x_776_ = lean_box(2);
v___x_777_ = ((size_t)31ULL);
v___x_778_ = lean_usize_land(v_x_773_, v___x_777_);
v_j_779_ = lean_usize_to_nat(v___x_778_);
v___x_780_ = lean_array_get_borrowed(v___x_776_, v_es_775_, v_j_779_);
lean_dec(v_j_779_);
switch(lean_obj_tag(v___x_780_))
{
case 0:
{
lean_object* v_key_781_; uint8_t v___x_782_; 
v_key_781_ = lean_ctor_get(v___x_780_, 0);
v___x_782_ = l_Lean_instBEqMVarId_beq(v_x_774_, v_key_781_);
return v___x_782_;
}
case 1:
{
lean_object* v_node_783_; size_t v___x_784_; size_t v___x_785_; 
v_node_783_ = lean_ctor_get(v___x_780_, 0);
v___x_784_ = ((size_t)5ULL);
v___x_785_ = lean_usize_shift_right(v_x_773_, v___x_784_);
v_x_772_ = v_node_783_;
v_x_773_ = v___x_785_;
goto _start;
}
default: 
{
uint8_t v___x_787_; 
v___x_787_ = 0;
return v___x_787_;
}
}
}
else
{
lean_object* v_ks_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_ks_788_ = lean_ctor_get(v_x_772_, 0);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_788_, v___x_789_, v_x_774_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
size_t v_x_9681__boxed_794_; uint8_t v_res_795_; lean_object* v_r_796_; 
v_x_9681__boxed_794_ = lean_unbox_usize(v_x_792_);
lean_dec(v_x_792_);
v_res_795_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_791_, v_x_9681__boxed_794_, v_x_793_);
lean_dec(v_x_793_);
lean_dec_ref(v_x_791_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint64_t v___x_799_; size_t v___x_800_; uint8_t v___x_801_; 
v___x_799_ = l_Lean_instHashableMVarId_hash(v_x_798_);
v___x_800_ = lean_uint64_to_usize(v___x_799_);
v___x_801_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_797_, v___x_800_, v_x_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_802_, v_x_803_);
lean_dec(v_x_803_);
lean_dec_ref(v_x_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v_mctx_810_; lean_object* v_eAssignment_811_; uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_809_ = lean_st_ref_get(v___y_807_);
v_mctx_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_mctx_810_);
lean_dec(v___x_809_);
v_eAssignment_811_ = lean_ctor_get(v_mctx_810_, 8);
lean_inc_ref(v_eAssignment_811_);
lean_dec_ref(v_mctx_810_);
v___x_812_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_811_, v_mvarId_806_);
lean_dec_ref(v_eAssignment_811_);
v___x_813_ = lean_box(v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec(v_mvarId_815_);
return v_res_818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_829_ = l_Lean_mkConst(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_box(0);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_837_ = l_Lean_mkConst(v___x_836_, v___x_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_mvarId_850_; lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_905_; 
v___x_849_ = lean_st_ref_get(v_a_838_);
v_mvarId_850_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_mvarId_850_);
lean_dec(v___x_849_);
v___x_851_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_850_, v_a_845_);
lean_dec(v_mvarId_850_);
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_905_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_905_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_905_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; 
v___x_856_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_del_object(v___x_854_);
v___x_857_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_842_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_858_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v___x_861_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_842_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_861_, 1);
v___x_863_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_842_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_867_ = l_Lean_mkApp4(v___x_865_, v_a_862_, v_a_864_, v_a_860_, v___x_866_);
v___x_868_ = l_Lean_Meta_Grind_closeGoal(v___x_867_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_a_862_);
lean_dec(v_a_860_);
v_a_869_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_863_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_863_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec(v_a_860_);
v_a_877_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_861_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_861_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_859_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_859_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_857_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_857_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_901_);
v___x_903_ = v___x_854_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_918_, v___y_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v_mvarId_931_);
return v_res_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_945_, v_x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_948_, v_x_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_x_949_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_953_, lean_object* v_x_954_, size_t v_x_955_, lean_object* v_x_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_954_, v_x_955_, v_x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
size_t v_x_9964__boxed_962_; uint8_t v_res_963_; lean_object* v_r_964_; 
v_x_9964__boxed_962_ = lean_unbox_usize(v_x_960_);
lean_dec(v_x_960_);
v_res_963_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_958_, v_x_959_, v_x_9964__boxed_962_, v_x_961_);
lean_dec(v_x_961_);
lean_dec_ref(v_x_959_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_965_, lean_object* v_keys_966_, lean_object* v_vals_967_, lean_object* v_heq_968_, lean_object* v_i_969_, lean_object* v_k_970_){
_start:
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_966_, v_i_969_, v_k_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_972_, lean_object* v_keys_973_, lean_object* v_vals_974_, lean_object* v_heq_975_, lean_object* v_i_976_, lean_object* v_k_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_972_, v_keys_973_, v_vals_974_, v_heq_975_, v_i_976_, v_k_977_);
lean_dec(v_k_977_);
lean_dec_ref(v_vals_974_);
lean_dec_ref(v_keys_973_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_986_, lean_object* v_rhs_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; 
lean_inc_ref(v_rhs_987_);
lean_inc_ref(v_lhs_986_);
v___x_999_ = l_Lean_Meta_mkEq(v_lhs_986_, v_rhs_987_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
lean_inc(v_a_997_);
lean_inc_ref(v_a_996_);
lean_inc(v_a_995_);
lean_inc_ref(v_a_994_);
lean_inc(v_a_993_);
lean_inc_ref(v_a_992_);
lean_inc(v_a_991_);
lean_inc_ref(v_a_990_);
lean_inc(v_a_989_);
lean_inc(v_a_988_);
v___x_1001_ = lean_grind_mk_eq_proof(v_lhs_986_, v_rhs_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
lean_inc(v_a_1000_);
v___x_1003_ = l_Lean_Meta_mkDecide(v_a_1000_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1006_ = l_Lean_Expr_appArg_x21(v_a_1004_);
lean_dec(v_a_1004_);
v___x_1007_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_1000_);
v___x_1008_ = l_Lean_mkApp3(v___x_1005_, v_a_1000_, v___x_1006_, v___x_1007_);
v___x_1009_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_992_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1012_ = l_Lean_mkApp4(v___x_1011_, v_a_1000_, v_a_1010_, v___x_1008_, v_a_1002_);
v___x_1013_ = l_Lean_Meta_Grind_closeGoal(v___x_1012_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1013_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v___x_1008_);
lean_dec(v_a_1002_);
lean_dec(v_a_1000_);
v_a_1014_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1009_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1009_);
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
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1002_);
lean_dec(v_a_1000_);
v_a_1022_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1003_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1003_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1000_);
v_a_1030_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1001_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1001_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_rhs_987_);
lean_dec_ref(v_lhs_986_);
v_a_1038_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_999_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_999_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1046_, lean_object* v_rhs_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1046_, v_rhs_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1060_, lean_object* v_as_x27_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
if (lean_obj_tag(v_as_x27_1061_) == 0)
{
lean_object* v___x_1074_; 
lean_dec(v___x_1060_);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1062_);
return v___x_1074_;
}
else
{
lean_object* v_head_1075_; lean_object* v_tail_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_head_1075_ = lean_ctor_get(v_as_x27_1061_, 0);
v_tail_1076_ = lean_ctor_get(v_as_x27_1061_, 1);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_st_ref_get(v___y_1063_);
lean_inc(v_head_1075_);
v___x_1079_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1078_, v_head_1075_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v_self_1081_; lean_object* v_next_1082_; lean_object* v_root_1083_; lean_object* v_congr_1084_; lean_object* v_target_x3f_1085_; lean_object* v_proof_x3f_1086_; uint8_t v_flipped_1087_; lean_object* v_size_1088_; uint8_t v_interpreted_1089_; uint8_t v_ctor_1090_; uint8_t v_hasLambdas_1091_; uint8_t v_heqProofs_1092_; lean_object* v_idx_1093_; lean_object* v_generation_1094_; lean_object* v_mt_1095_; lean_object* v_sTerms_1096_; uint8_t v_funCC_1097_; lean_object* v_ematchDiagSource_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1110_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_self_1081_ = lean_ctor_get(v_a_1080_, 0);
v_next_1082_ = lean_ctor_get(v_a_1080_, 1);
v_root_1083_ = lean_ctor_get(v_a_1080_, 2);
v_congr_1084_ = lean_ctor_get(v_a_1080_, 3);
v_target_x3f_1085_ = lean_ctor_get(v_a_1080_, 4);
v_proof_x3f_1086_ = lean_ctor_get(v_a_1080_, 5);
v_flipped_1087_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12);
v_size_1088_ = lean_ctor_get(v_a_1080_, 6);
v_interpreted_1089_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12 + 1);
v_ctor_1090_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12 + 2);
v_hasLambdas_1091_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12 + 3);
v_heqProofs_1092_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12 + 4);
v_idx_1093_ = lean_ctor_get(v_a_1080_, 7);
v_generation_1094_ = lean_ctor_get(v_a_1080_, 8);
v_mt_1095_ = lean_ctor_get(v_a_1080_, 9);
v_sTerms_1096_ = lean_ctor_get(v_a_1080_, 10);
v_funCC_1097_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1098_ = lean_ctor_get(v_a_1080_, 11);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_a_1080_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1100_ = v_a_1080_;
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_ematchDiagSource_1098_);
lean_inc(v_sTerms_1096_);
lean_inc(v_mt_1095_);
lean_inc(v_generation_1094_);
lean_inc(v_idx_1093_);
lean_inc(v_size_1088_);
lean_inc(v_proof_x3f_1086_);
lean_inc(v_target_x3f_1085_);
lean_inc(v_congr_1084_);
lean_inc(v_root_1083_);
lean_inc(v_next_1082_);
lean_inc(v_self_1081_);
lean_dec(v_a_1080_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1110_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_nat_dec_lt(v_mt_1095_, v___x_1060_);
lean_dec(v_mt_1095_);
if (v___x_1102_ == 0)
{
lean_del_object(v___x_1100_);
lean_dec(v_ematchDiagSource_1098_);
lean_dec(v_sTerms_1096_);
lean_dec(v_generation_1094_);
lean_dec(v_idx_1093_);
lean_dec(v_size_1088_);
lean_dec(v_proof_x3f_1086_);
lean_dec(v_target_x3f_1085_);
lean_dec_ref(v_congr_1084_);
lean_dec_ref(v_root_1083_);
lean_dec_ref(v_next_1082_);
lean_dec_ref(v_self_1081_);
v_as_x27_1061_ = v_tail_1076_;
v_b_1062_ = v___x_1077_;
goto _start;
}
else
{
lean_object* v___x_1105_; 
lean_inc(v___x_1060_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 9, v___x_1060_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_self_1081_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_next_1082_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_root_1083_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_congr_1084_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_target_x3f_1085_);
lean_ctor_set(v_reuseFailAlloc_1109_, 5, v_proof_x3f_1086_);
lean_ctor_set(v_reuseFailAlloc_1109_, 6, v_size_1088_);
lean_ctor_set(v_reuseFailAlloc_1109_, 7, v_idx_1093_);
lean_ctor_set(v_reuseFailAlloc_1109_, 8, v_generation_1094_);
lean_ctor_set(v_reuseFailAlloc_1109_, 9, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1109_, 10, v_sTerms_1096_);
lean_ctor_set(v_reuseFailAlloc_1109_, 11, v_ematchDiagSource_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12, v_flipped_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12 + 1, v_interpreted_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12 + 2, v_ctor_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12 + 3, v_hasLambdas_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12 + 4, v_heqProofs_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*12 + 5, v_funCC_1097_);
v___x_1105_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
lean_inc(v_head_1075_);
v___x_1106_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1075_, v___x_1105_, v___y_1063_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref_known(v___x_1106_, 1);
v___x_1107_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1075_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
v_as_x27_1061_ = v_tail_1076_;
v_b_1062_ = v___x_1077_;
goto _start;
}
else
{
lean_dec(v___x_1060_);
return v___x_1107_;
}
}
else
{
lean_dec(v___x_1060_);
return v___x_1106_;
}
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v___x_1060_);
v_a_1111_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1079_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1079_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_toGoalState_1132_; lean_object* v_ematch_1133_; lean_object* v_gmt_1134_; lean_object* v___x_1135_; 
v___x_1131_ = lean_st_ref_get(v_a_1120_);
v_toGoalState_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_toGoalState_1132_);
lean_dec(v___x_1131_);
v_ematch_1133_ = lean_ctor_get(v_toGoalState_1132_, 13);
lean_inc_ref(v_ematch_1133_);
lean_dec_ref(v_toGoalState_1132_);
v_gmt_1134_ = lean_ctor_get(v_ematch_1133_, 1);
lean_inc(v_gmt_1134_);
lean_dec_ref(v_ematch_1133_);
v___x_1135_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1136_);
lean_dec(v_a_1136_);
v___x_1138_ = lean_box(0);
v___x_1139_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1134_, v___x_1137_, v___x_1138_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v___x_1137_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1147_);
v___x_1141_ = v___x_1139_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1138_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1138_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
return v___x_1139_;
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_gmt_1134_);
v_a_1148_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1135_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1135_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_root_1156_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1169_, lean_object* v_as_x27_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1169_, v_as_x27_1170_, v_b_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v_as_x27_1170_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1184_, lean_object* v_as_1185_, lean_object* v_as_x27_1186_, lean_object* v_b_1187_, lean_object* v_a_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1184_, v_as_x27_1186_, v_b_1187_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1201_, lean_object* v_as_1202_, lean_object* v_as_x27_1203_, lean_object* v_b_1204_, lean_object* v_a_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1201_, v_as_1202_, v_as_x27_1203_, v_b_1204_, v_a_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v_as_x27_1203_);
lean_dec(v_as_1202_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = l_List_reverse___redArg(v_a_1219_);
return v___x_1220_;
}
else
{
lean_object* v_head_1221_; lean_object* v_tail_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1231_; 
v_head_1221_ = lean_ctor_get(v_a_1218_, 0);
v_tail_1222_ = lean_ctor_get(v_a_1218_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1224_ = v_a_1218_;
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_tail_1222_);
lean_inc(v_head_1221_);
lean_dec(v_a_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l_Lean_MessageData_ofExpr(v_head_1221_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_a_1219_);
lean_ctor_set(v___x_1224_, 0, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_a_1219_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v_a_1218_ = v_tail_1222_;
v_a_1219_ = v___x_1228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1232_, lean_object* v_a_1233_, lean_object* v_fst_1234_, lean_object* v_a_1235_, lean_object* v_lams_1236_, lean_object* v_____r_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1232_, v_a_1235_, v___y_1238_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
goto v___jp_1249_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_inc(v_fst_1234_);
v___x_1289_ = l_Array_reverse___redArg(v_fst_1234_);
lean_inc(v_snd_1232_);
v___x_1290_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1236_, v_snd_1232_, v___x_1289_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_dec_ref_known(v___x_1290_, 1);
goto v___jp_1249_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_fst_1234_);
lean_dec(v_snd_1232_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
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
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v_fst_1234_);
lean_dec(v_snd_1232_);
v_a_1299_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1286_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1286_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
v___jp_1249_:
{
if (lean_obj_tag(v_snd_1232_) == 5)
{
lean_object* v_fn_1250_; lean_object* v_arg_1251_; lean_object* v___x_1252_; 
v_fn_1250_ = lean_ctor_get(v_snd_1232_, 0);
lean_inc_ref(v_fn_1250_);
v_arg_1251_ = lean_ctor_get(v_snd_1232_, 1);
lean_inc_ref(v_arg_1251_);
v___x_1252_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1233_, v___y_1238_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = lean_box(0);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc(v___y_1238_);
v___x_1255_ = lean_grind_internalize(v_snd_1232_, v_a_1253_, v___x_1254_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1266_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1259_ = lean_array_push(v_fst_1234_, v_arg_1251_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_fn_1250_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1261_);
v___x_1263_ = v___x_1257_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_arg_1251_);
lean_dec_ref(v_fn_1250_);
lean_dec(v_fst_1234_);
v_a_1267_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1255_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1255_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec_ref(v_arg_1251_);
lean_dec_ref(v_fn_1250_);
lean_dec_ref_known(v_snd_1232_, 2);
lean_dec(v_fst_1234_);
v_a_1275_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1252_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1252_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_fst_1234_);
lean_ctor_set(v___x_1283_, 1, v_snd_1232_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1307_ = _args[0];
lean_object* v_a_1308_ = _args[1];
lean_object* v_fst_1309_ = _args[2];
lean_object* v_a_1310_ = _args[3];
lean_object* v_lams_1311_ = _args[4];
lean_object* v_____r_1312_ = _args[5];
lean_object* v___y_1313_ = _args[6];
lean_object* v___y_1314_ = _args[7];
lean_object* v___y_1315_ = _args[8];
lean_object* v___y_1316_ = _args[9];
lean_object* v___y_1317_ = _args[10];
lean_object* v___y_1318_ = _args[11];
lean_object* v___y_1319_ = _args[12];
lean_object* v___y_1320_ = _args[13];
lean_object* v___y_1321_ = _args[14];
lean_object* v___y_1322_ = _args[15];
lean_object* v___y_1323_ = _args[16];
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1307_, v_a_1308_, v_fst_1309_, v_a_1310_, v_lams_1311_, v_____r_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v_lams_1311_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_a_1308_);
return v_res_1324_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1332_ = l_Lean_Name_append(v___x_1331_, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_lams_1338_, lean_object* v_a_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___y_1352_; lean_object* v_toCold_1372_; lean_object* v_options_1373_; lean_object* v_fst_1374_; lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1412_; 
v_toCold_1372_ = lean_ctor_get(v___y_1348_, 0);
v_options_1373_ = lean_ctor_get(v_toCold_1372_, 2);
v_fst_1374_ = lean_ctor_get(v_a_1339_, 0);
v_snd_1375_ = lean_ctor_get(v_a_1339_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_a_1339_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1377_ = v_a_1339_;
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_inc(v_fst_1374_);
lean_dec(v_a_1339_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1412_;
goto v_resetjp_1376_;
}
v___jp_1351_:
{
if (lean_obj_tag(v___y_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1363_; 
v_a_1353_ = lean_ctor_get(v___y_1352_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___y_1352_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1355_ = v___y_1352_;
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___y_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
if (lean_obj_tag(v_a_1353_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; 
v_a_1357_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v_a_1353_, 1);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_a_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
else
{
lean_object* v_a_1361_; 
lean_del_object(v___x_1355_);
v_a_1361_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v_a_1353_, 1);
v_a_1339_ = v_a_1361_;
goto _start;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___y_1352_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___y_1352_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___y_1352_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___y_1352_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
v_resetjp_1376_:
{
lean_object* v_inheritedTraceOptions_1379_; uint8_t v_hasTrace_1380_; 
v_inheritedTraceOptions_1379_ = lean_ctor_get(v_toCold_1372_, 11);
v_hasTrace_1380_ = lean_ctor_get_uint8(v_options_1373_, sizeof(void*)*1);
if (v_hasTrace_1380_ == 0)
{
lean_del_object(v___x_1377_);
goto v___jp_1381_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1385_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1386_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1379_, v_options_1373_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_del_object(v___x_1377_);
goto v___jp_1381_;
}
else
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Meta_Grind_updateLastTag(v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec_ref_known(v___x_1387_, 1);
v___x_1388_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1375_);
v___x_1389_ = l_Lean_MessageData_ofExpr(v_snd_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 7);
lean_ctor_set(v___x_1377_, 1, v___x_1389_);
lean_ctor_set(v___x_1377_, 0, v___x_1388_);
v___x_1391_ = v___x_1377_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1384_, v___x_1391_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1375_, v_a_1336_, v_fst_1374_, v_a_1337_, v_lams_1338_, v_a_1393_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
v___y_1352_ = v___x_1394_;
goto v___jp_1351_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_snd_1375_);
lean_dec(v_fst_1374_);
v_a_1395_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1392_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1392_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
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
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_del_object(v___x_1377_);
lean_dec(v_snd_1375_);
lean_dec(v_fst_1374_);
v_a_1404_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1387_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1387_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
v___jp_1381_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1375_, v_a_1336_, v_fst_1374_, v_a_1337_, v_lams_1338_, v___x_1382_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
v___y_1352_ = v___x_1383_;
goto v___jp_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_lams_1415_, lean_object* v_a_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1413_, v_a_1414_, v_lams_1415_, v_a_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v_lams_1415_);
lean_dec_ref(v_a_1414_);
lean_dec_ref(v_a_1413_);
return v_res_1428_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1433_ = l_Lean_stringToMessageData(v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1434_, lean_object* v_lams_1435_, lean_object* v_as_x27_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
if (lean_obj_tag(v_as_x27_1436_) == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_b_1437_);
return v___x_1449_;
}
else
{
lean_object* v_toCold_1450_; lean_object* v_options_1451_; lean_object* v_head_1452_; lean_object* v_tail_1453_; lean_object* v_inheritedTraceOptions_1454_; uint8_t v_hasTrace_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; 
v_toCold_1450_ = lean_ctor_get(v___y_1446_, 0);
v_options_1451_ = lean_ctor_get(v_toCold_1450_, 2);
v_head_1452_ = lean_ctor_get(v_as_x27_1436_, 0);
v_tail_1453_ = lean_ctor_get(v_as_x27_1436_, 1);
v_inheritedTraceOptions_1454_ = lean_ctor_get(v_toCold_1450_, 11);
v_hasTrace_1455_ = lean_ctor_get_uint8(v_options_1451_, sizeof(void*)*1);
v___x_1456_ = lean_box(0);
v___x_1457_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1455_ == 0)
{
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1481_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1454_, v_options_1451_, v___x_1481_);
if (v___x_1482_ == 0)
{
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Meta_Grind_updateLastTag(v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref_known(v___x_1483_, 1);
v___x_1484_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1452_);
v___x_1485_ = l_Lean_MessageData_ofExpr(v_head_1452_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1480_, v___x_1486_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec_ref_known(v___x_1487_, 1);
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
goto v___jp_1458_;
}
else
{
return v___x_1487_;
}
}
else
{
return v___x_1483_;
}
}
}
v___jp_1458_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_inc(v_head_1452_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1457_);
lean_ctor_set(v___x_1469_, 1, v_head_1452_);
v___x_1470_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1452_, v_a_1434_, v_lams_1435_, v___x_1469_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_dec_ref_known(v___x_1470_, 1);
v_as_x27_1436_ = v_tail_1453_;
v_b_1437_ = v___x_1456_;
goto _start;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1470_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1470_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1488_, lean_object* v_lams_1489_, lean_object* v_as_x27_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1488_, v_lams_1489_, v_as_x27_1490_, v_b_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v_as_x27_1490_);
lean_dec_ref(v_lams_1489_);
lean_dec_ref(v_a_1488_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1504_, lean_object* v_lams_1505_, lean_object* v_as_1506_, lean_object* v_as_x27_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
if (lean_obj_tag(v_as_x27_1507_) == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_b_1508_);
return v___x_1520_;
}
else
{
lean_object* v_toCold_1521_; lean_object* v_options_1522_; lean_object* v_head_1523_; lean_object* v_tail_1524_; lean_object* v_inheritedTraceOptions_1525_; uint8_t v_hasTrace_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; 
v_toCold_1521_ = lean_ctor_get(v___y_1517_, 0);
v_options_1522_ = lean_ctor_get(v_toCold_1521_, 2);
v_head_1523_ = lean_ctor_get(v_as_x27_1507_, 0);
v_tail_1524_ = lean_ctor_get(v_as_x27_1507_, 1);
v_inheritedTraceOptions_1525_ = lean_ctor_get(v_toCold_1521_, 11);
v_hasTrace_1526_ = lean_ctor_get_uint8(v_options_1522_, sizeof(void*)*1);
v___x_1527_ = lean_box(0);
v___x_1528_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1526_ == 0)
{
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1552_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1553_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1525_, v_options_1522_, v___x_1552_);
if (v___x_1553_ == 0)
{
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Meta_Grind_updateLastTag(v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref_known(v___x_1554_, 1);
v___x_1555_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1523_);
v___x_1556_ = l_Lean_MessageData_ofExpr(v_head_1523_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1551_, v___x_1557_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
goto v___jp_1529_;
}
else
{
return v___x_1558_;
}
}
else
{
return v___x_1554_;
}
}
}
v___jp_1529_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_inc(v_head_1523_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1528_);
lean_ctor_set(v___x_1540_, 1, v_head_1523_);
v___x_1541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1523_, v_a_1504_, v_lams_1505_, v___x_1540_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v___x_1541_, 1);
v___x_1542_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1504_, v_lams_1505_, v_tail_1524_, v___x_1527_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1542_;
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1541_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1559_, lean_object* v_lams_1560_, lean_object* v_as_1561_, lean_object* v_as_x27_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1559_, v_lams_1560_, v_as_1561_, v_as_x27_1562_, v_b_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v_as_x27_1562_);
lean_dec(v_as_1561_);
lean_dec_ref(v_lams_1560_);
lean_dec_ref(v_a_1559_);
return v_res_1575_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1582_, lean_object* v_lams_1583_, lean_object* v_as_1584_, size_t v_sz_1585_, size_t v_i_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_b_1587_);
return v___x_1600_;
}
else
{
lean_object* v_toCold_1601_; lean_object* v_options_1602_; lean_object* v_inheritedTraceOptions_1603_; uint8_t v_hasTrace_1604_; lean_object* v___x_1605_; lean_object* v_a_1606_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; 
v_toCold_1601_ = lean_ctor_get(v___y_1596_, 0);
v_options_1602_ = lean_ctor_get(v_toCold_1601_, 2);
v_inheritedTraceOptions_1603_ = lean_ctor_get(v_toCold_1601_, 11);
v_hasTrace_1604_ = lean_ctor_get_uint8(v_options_1602_, sizeof(void*)*1);
v___x_1605_ = lean_box(0);
v_a_1606_ = lean_array_uget_borrowed(v_as_1584_, v_i_1586_);
if (v_hasTrace_1604_ == 0)
{
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1634_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1635_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1603_, v_options_1602_, v___x_1634_);
if (v___x_1635_ == 0)
{
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_updateLastTag(v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref_known(v___x_1636_, 1);
v___x_1637_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1606_, v___y_1588_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1606_);
v___x_1640_ = l_Lean_MessageData_ofExpr(v_a_1606_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1638_);
lean_dec(v_a_1638_);
v___x_1645_ = lean_box(0);
v___x_1646_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1644_, v___x_1645_);
v___x_1647_ = l_Lean_MessageData_ofList(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1643_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1633_, v___x_1648_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec_ref_known(v___x_1649_, 1);
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
goto v___jp_1607_;
}
else
{
return v___x_1649_;
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1637_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1637_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
return v___x_1636_;
}
}
}
v___jp_1607_:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1606_, v___y_1608_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1619_);
lean_dec(v_a_1619_);
v___x_1621_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1582_, v_lams_1583_, v___x_1620_, v___x_1620_, v___x_1605_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___x_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
size_t v___x_1622_; size_t v___x_1623_; 
lean_dec_ref_known(v___x_1621_, 1);
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1586_, v___x_1622_);
v_i_1586_ = v___x_1623_;
v_b_1587_ = v___x_1605_;
goto _start;
}
else
{
return v___x_1621_;
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1618_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1618_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1658_ = _args[0];
lean_object* v_lams_1659_ = _args[1];
lean_object* v_as_1660_ = _args[2];
lean_object* v_sz_1661_ = _args[3];
lean_object* v_i_1662_ = _args[4];
lean_object* v_b_1663_ = _args[5];
lean_object* v___y_1664_ = _args[6];
lean_object* v___y_1665_ = _args[7];
lean_object* v___y_1666_ = _args[8];
lean_object* v___y_1667_ = _args[9];
lean_object* v___y_1668_ = _args[10];
lean_object* v___y_1669_ = _args[11];
lean_object* v___y_1670_ = _args[12];
lean_object* v___y_1671_ = _args[13];
lean_object* v___y_1672_ = _args[14];
lean_object* v___y_1673_ = _args[15];
lean_object* v___y_1674_ = _args[16];
_start:
{
size_t v_sz_boxed_1675_; size_t v_i_boxed_1676_; lean_object* v_res_1677_; 
v_sz_boxed_1675_ = lean_unbox_usize(v_sz_1661_);
lean_dec(v_sz_1661_);
v_i_boxed_1676_ = lean_unbox_usize(v_i_1662_);
lean_dec(v_i_1662_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1658_, v_lams_1659_, v_as_1660_, v_sz_boxed_1675_, v_i_boxed_1676_, v_b_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v_as_1660_);
lean_dec_ref(v_lams_1659_);
lean_dec_ref(v_a_1658_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1678_, lean_object* v_lams_1679_, lean_object* v_as_1680_, size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_b_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_b_1683_);
return v___x_1696_;
}
else
{
lean_object* v_toCold_1697_; lean_object* v_options_1698_; lean_object* v_inheritedTraceOptions_1699_; uint8_t v_hasTrace_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; 
v_toCold_1697_ = lean_ctor_get(v___y_1692_, 0);
v_options_1698_ = lean_ctor_get(v_toCold_1697_, 2);
v_inheritedTraceOptions_1699_ = lean_ctor_get(v_toCold_1697_, 11);
v_hasTrace_1700_ = lean_ctor_get_uint8(v_options_1698_, sizeof(void*)*1);
v___x_1701_ = lean_box(0);
v_a_1702_ = lean_array_uget_borrowed(v_as_1680_, v_i_1682_);
if (v_hasTrace_1700_ == 0)
{
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1730_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1699_, v_options_1698_, v___x_1730_);
if (v___x_1731_ == 0)
{
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Meta_Grind_updateLastTag(v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1733_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1702_, v___y_1684_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1702_);
v___x_1736_ = l_Lean_MessageData_ofExpr(v_a_1702_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1734_);
lean_dec(v_a_1734_);
v___x_1741_ = lean_box(0);
v___x_1742_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1740_, v___x_1741_);
v___x_1743_ = l_Lean_MessageData_ofList(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1739_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1729_, v___x_1744_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_dec_ref_known(v___x_1745_, 1);
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
goto v___jp_1703_;
}
else
{
return v___x_1745_;
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1733_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1733_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
return v___x_1732_;
}
}
}
v___jp_1703_:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1702_, v___y_1704_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1715_);
lean_dec(v_a_1715_);
v___x_1717_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1678_, v_lams_1679_, v___x_1716_, v___x_1716_, v___x_1701_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1717_, 1);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1682_, v___x_1718_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1678_, v_lams_1679_, v_as_1680_, v_sz_1681_, v___x_1719_, v___x_1701_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1720_;
}
else
{
return v___x_1717_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
v_a_1721_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1714_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1714_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1754_ = _args[0];
lean_object* v_lams_1755_ = _args[1];
lean_object* v_as_1756_ = _args[2];
lean_object* v_sz_1757_ = _args[3];
lean_object* v_i_1758_ = _args[4];
lean_object* v_b_1759_ = _args[5];
lean_object* v___y_1760_ = _args[6];
lean_object* v___y_1761_ = _args[7];
lean_object* v___y_1762_ = _args[8];
lean_object* v___y_1763_ = _args[9];
lean_object* v___y_1764_ = _args[10];
lean_object* v___y_1765_ = _args[11];
lean_object* v___y_1766_ = _args[12];
lean_object* v___y_1767_ = _args[13];
lean_object* v___y_1768_ = _args[14];
lean_object* v___y_1769_ = _args[15];
lean_object* v___y_1770_ = _args[16];
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; lean_object* v_res_1773_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1757_);
lean_dec(v_sz_1757_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1758_);
lean_dec(v_i_1758_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1754_, v_lams_1755_, v_as_1756_, v_sz_boxed_1771_, v_i_boxed_1772_, v_b_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v_as_1756_);
lean_dec_ref(v_lams_1755_);
lean_dec_ref(v_a_1754_);
return v_res_1773_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1780_, lean_object* v_fns_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = lean_array_get_size(v_lams_1780_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_nat_dec_eq(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1796_ = l_Lean_instInhabitedExpr;
v___x_1797_ = lean_unsigned_to_nat(1u);
v___x_1798_ = lean_nat_sub(v___x_1793_, v___x_1797_);
v___x_1799_ = lean_array_get_borrowed(v___x_1796_, v_lams_1780_, v___x_1798_);
lean_dec(v___x_1798_);
v___x_1800_ = lean_st_ref_get(v_a_1782_);
lean_inc(v___x_1799_);
v___x_1801_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1800_, v___x_1799_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v___x_1800_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v_toCold_1826_; lean_object* v_options_1827_; uint8_t v_hasTrace_1828_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v_toCold_1826_ = lean_ctor_get(v_a_1790_, 0);
v_options_1827_ = lean_ctor_get(v_toCold_1826_, 2);
v_hasTrace_1828_ = lean_ctor_get_uint8(v_options_1827_, sizeof(void*)*1);
if (v_hasTrace_1828_ == 0)
{
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
goto v___jp_1803_;
}
else
{
lean_object* v_inheritedTraceOptions_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_inheritedTraceOptions_1829_ = lean_ctor_get(v_toCold_1826_, 11);
v___x_1830_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1831_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1829_, v_options_1827_, v___x_1831_);
if (v___x_1832_ == 0)
{
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_Grind_updateLastTag(v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1833_, 1);
v___x_1834_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1781_);
v___x_1835_ = lean_array_to_list(v_fns_1781_);
v___x_1836_ = lean_box(0);
v___x_1837_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1835_, v___x_1836_);
v___x_1838_ = l_Lean_MessageData_ofList(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1834_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
lean_inc_ref(v_lams_1780_);
v___x_1842_ = lean_array_to_list(v_lams_1780_);
v___x_1843_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1842_, v___x_1836_);
v___x_1844_ = l_Lean_MessageData_ofList(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1841_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1830_, v___x_1845_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
goto v___jp_1803_;
}
else
{
lean_dec(v_a_1802_);
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
return v___x_1846_;
}
}
else
{
lean_dec(v_a_1802_);
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
return v___x_1833_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1814_; size_t v_sz_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1814_ = lean_box(0);
v_sz_1815_ = lean_array_size(v_fns_1781_);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1802_, v_lams_1780_, v_fns_1781_, v_sz_1815_, v___x_1816_, v___x_1814_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
lean_dec(v_a_1802_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1817_, 0);
lean_dec(v_unused_1825_);
v___x_1819_ = v___x_1817_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v___x_1817_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1814_);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1814_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
v_a_1847_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1801_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1801_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1857_, lean_object* v_fns_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1857_, v_fns_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec(v_a_1859_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_lams_1873_, lean_object* v_inst_1874_, lean_object* v_a_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1871_, v_a_1872_, v_lams_1873_, v_a_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_lams_1890_, lean_object* v_inst_1891_, lean_object* v_a_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1888_, v_a_1889_, v_lams_1890_, v_inst_1891_, v_a_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v_lams_1890_);
lean_dec_ref(v_a_1889_);
lean_dec_ref(v_a_1888_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1905_, lean_object* v_lams_1906_, lean_object* v_as_1907_, lean_object* v_as_x27_1908_, lean_object* v_b_1909_, lean_object* v_a_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1905_, v_lams_1906_, v_as_1907_, v_as_x27_1908_, v_b_1909_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1923_ = _args[0];
lean_object* v_lams_1924_ = _args[1];
lean_object* v_as_1925_ = _args[2];
lean_object* v_as_x27_1926_ = _args[3];
lean_object* v_b_1927_ = _args[4];
lean_object* v_a_1928_ = _args[5];
lean_object* v___y_1929_ = _args[6];
lean_object* v___y_1930_ = _args[7];
lean_object* v___y_1931_ = _args[8];
lean_object* v___y_1932_ = _args[9];
lean_object* v___y_1933_ = _args[10];
lean_object* v___y_1934_ = _args[11];
lean_object* v___y_1935_ = _args[12];
lean_object* v___y_1936_ = _args[13];
lean_object* v___y_1937_ = _args[14];
lean_object* v___y_1938_ = _args[15];
lean_object* v___y_1939_ = _args[16];
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1923_, v_lams_1924_, v_as_1925_, v_as_x27_1926_, v_b_1927_, v_a_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v_as_x27_1926_);
lean_dec(v_as_1925_);
lean_dec_ref(v_lams_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1941_, lean_object* v_lams_1942_, lean_object* v_as_1943_, lean_object* v_as_x27_1944_, lean_object* v_b_1945_, lean_object* v_a_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1941_, v_lams_1942_, v_as_x27_1944_, v_b_1945_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1959_ = _args[0];
lean_object* v_lams_1960_ = _args[1];
lean_object* v_as_1961_ = _args[2];
lean_object* v_as_x27_1962_ = _args[3];
lean_object* v_b_1963_ = _args[4];
lean_object* v_a_1964_ = _args[5];
lean_object* v___y_1965_ = _args[6];
lean_object* v___y_1966_ = _args[7];
lean_object* v___y_1967_ = _args[8];
lean_object* v___y_1968_ = _args[9];
lean_object* v___y_1969_ = _args[10];
lean_object* v___y_1970_ = _args[11];
lean_object* v___y_1971_ = _args[12];
lean_object* v___y_1972_ = _args[13];
lean_object* v___y_1973_ = _args[14];
lean_object* v___y_1974_ = _args[15];
lean_object* v___y_1975_ = _args[16];
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1959_, v_lams_1960_, v_as_1961_, v_as_x27_1962_, v_b_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v_as_x27_1962_);
lean_dec(v_as_1961_);
lean_dec_ref(v_lams_1960_);
lean_dec_ref(v_a_1959_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1980_, lean_object* v_as_1981_, size_t v_sz_1982_, size_t v_i_1983_, lean_object* v_b_1984_){
_start:
{
lean_object* v_a_1986_; uint8_t v___x_1990_; 
v___x_1990_ = lean_usize_dec_lt(v_i_1983_, v_sz_1982_);
if (v___x_1990_ == 0)
{
lean_inc_ref(v_b_1984_);
return v_b_1984_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v_a_1993_; 
v___x_1991_ = lean_box(0);
v___x_1992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1993_ = lean_array_uget_borrowed(v_as_1981_, v_i_1983_);
if (lean_obj_tag(v_a_1993_) == 6)
{
lean_object* v_binderType_1994_; size_t v___x_1995_; size_t v___x_1996_; uint8_t v___x_1997_; 
v_binderType_1994_ = lean_ctor_get(v_a_1993_, 1);
v___x_1995_ = lean_ptr_addr(v_d_1980_);
v___x_1996_ = lean_ptr_addr(v_binderType_1994_);
v___x_1997_ = lean_usize_dec_eq(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
v_a_1986_ = v___x_1992_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_inc_ref(v_a_1993_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_a_1993_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v___x_1991_);
return v___x_2000_;
}
}
else
{
v_a_1986_ = v___x_1992_;
goto v___jp_1985_;
}
}
v___jp_1985_:
{
size_t v___x_1987_; size_t v___x_1988_; 
v___x_1987_ = ((size_t)1ULL);
v___x_1988_ = lean_usize_add(v_i_1983_, v___x_1987_);
v_i_1983_ = v___x_1988_;
v_b_1984_ = v_a_1986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2001_, lean_object* v_as_2002_, lean_object* v_sz_2003_, lean_object* v_i_2004_, lean_object* v_b_2005_){
_start:
{
size_t v_sz_boxed_2006_; size_t v_i_boxed_2007_; lean_object* v_res_2008_; 
v_sz_boxed_2006_ = lean_unbox_usize(v_sz_2003_);
lean_dec(v_sz_2003_);
v_i_boxed_2007_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2001_, v_as_2002_, v_sz_boxed_2006_, v_i_boxed_2007_, v_b_2005_);
lean_dec_ref(v_b_2005_);
lean_dec_ref(v_as_2002_);
lean_dec_ref(v_d_2001_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2009_, lean_object* v_d_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; size_t v_sz_2013_; size_t v___x_2014_; lean_object* v___x_2015_; lean_object* v_fst_2016_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2013_ = lean_array_size(v_lams_2009_);
v___x_2014_ = ((size_t)0ULL);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2010_, v_lams_2009_, v_sz_2013_, v___x_2014_, v___x_2012_);
v_fst_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_fst_2016_);
lean_dec_ref(v___x_2015_);
if (lean_obj_tag(v_fst_2016_) == 0)
{
return v___x_2011_;
}
else
{
lean_object* v_val_2017_; 
v_val_2017_ = lean_ctor_get(v_fst_2016_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v_fst_2016_, 1);
return v_val_2017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2018_, lean_object* v_d_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2018_, v_d_2019_);
lean_dec_ref(v_d_2019_);
lean_dec_ref(v_lams_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2031_, lean_object* v_lams_u2081_2032_, lean_object* v_as_2033_, size_t v_sz_2034_, size_t v_i_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_a_2049_; uint8_t v___x_2053_; 
v___x_2053_ = lean_usize_dec_lt(v_i_2035_, v_sz_2034_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_b_2036_);
return v___x_2054_;
}
else
{
lean_object* v___x_2055_; lean_object* v_a_2056_; 
v___x_2055_ = lean_box(0);
v_a_2056_ = lean_array_uget_borrowed(v_as_2033_, v_i_2035_);
if (lean_obj_tag(v_a_2056_) == 6)
{
lean_object* v_binderType_2057_; lean_object* v_body_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_binderType_2057_ = lean_ctor_get(v_a_2056_, 1);
v_body_2058_ = lean_ctor_get(v_a_2056_, 2);
v___x_2059_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2057_);
v___x_2060_ = l_Lean_Meta_getLevel(v_binderType_2057_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2061_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
lean_inc_ref(v___x_2064_);
v___x_2065_ = l_Lean_mkConst(v___x_2062_, v___x_2064_);
lean_inc_ref(v_binderType_2057_);
v___x_2066_ = l_Lean_Expr_app___override(v___x_2065_, v_binderType_2057_);
v___x_2067_ = lean_box(0);
v___x_2068_ = l_Lean_Meta_synthInstance_x3f(v___x_2066_, v___x_2067_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
if (lean_obj_tag(v_a_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___x_2135_; 
v_val_2070_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v_a_2069_, 1);
v___x_2135_ = l_Lean_Expr_hasLooseBVars(v_body_2058_);
if (v___x_2135_ == 0)
{
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2064_);
v___x_2137_ = l_Lean_mkConst(v___x_2136_, v___x_2064_);
lean_inc_ref(v_binderType_2057_);
v___x_2138_ = l_Lean_Expr_app___override(v___x_2137_, v_binderType_2057_);
v___x_2139_ = l_Lean_Meta_synthInstance_x3f(v___x_2138_, v___x_2067_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
if (lean_obj_tag(v_a_2140_) == 0)
{
lean_dec(v_val_2070_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
else
{
lean_dec_ref_known(v_a_2140_, 1);
if (v___x_2135_ == 0)
{
lean_dec(v_val_2070_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
else
{
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_val_2070_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2141_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2139_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2139_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
v___jp_2071_:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2031_, v_binderType_2057_);
if (lean_obj_tag(v___x_2082_) == 1)
{
lean_object* v_val_2083_; 
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v___x_2082_, 1);
if (lean_obj_tag(v_val_2083_) == 6)
{
lean_object* v_binderType_2084_; lean_object* v_body_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_binderType_2084_ = lean_ctor_get(v_val_2083_, 1);
lean_inc_ref(v_binderType_2084_);
v_body_2085_ = lean_ctor_get(v_val_2083_, 2);
lean_inc_ref(v_body_2085_);
lean_dec_ref_known(v_val_2083_, 3);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2087_ = l_Lean_mkConst(v___x_2086_, v___x_2064_);
v___x_2088_ = l_Lean_mkAppB(v___x_2087_, v_binderType_2084_, v_val_2070_);
v___x_2089_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2088_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_expr_instantiate1(v_body_2058_, v_a_2090_);
v___x_2092_ = lean_expr_instantiate1(v_body_2085_, v_a_2090_);
lean_dec_ref(v_body_2085_);
v___x_2093_ = lean_array_fget_borrowed(v_lams_u2081_2032_, v___x_2059_);
v___x_2094_ = lean_array_fget_borrowed(v_lams_u2082_2031_, v___x_2059_);
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2080_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc(v___x_2094_);
lean_inc(v___x_2093_);
v___x_2095_ = lean_grind_mk_eq_proof(v___x_2093_, v___x_2094_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = l_Lean_Meta_mkCongrFun(v_a_2096_, v_a_2090_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_mkEq(v___x_2091_, v___x_2092_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_Meta_mkExpectedPropHint(v_a_2098_, v_a_2100_);
v___x_2102_ = l_Lean_Meta_Grind_pushNewFact(v___x_2101_, v___x_2059_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_dec_ref_known(v___x_2102_, 1);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
else
{
return v___x_2102_;
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_a_2098_);
v_a_2103_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2099_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2099_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v___x_2092_);
lean_dec_ref(v___x_2091_);
v_a_2111_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2097_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2097_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v___x_2092_);
lean_dec_ref(v___x_2091_);
lean_dec(v_a_2090_);
v_a_2119_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2095_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2095_);
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
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_body_2085_);
v_a_2127_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2089_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2089_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_dec(v_val_2083_);
lean_dec(v_val_2070_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
}
else
{
lean_dec(v___x_2082_);
lean_dec(v_val_2070_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
}
}
else
{
lean_dec(v_a_2069_);
lean_dec_ref_known(v___x_2064_, 2);
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref_known(v___x_2064_, 2);
v_a_2149_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2068_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2068_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
v_a_2157_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2060_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2060_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
v_a_2049_ = v___x_2055_;
goto v___jp_2048_;
}
}
v___jp_2048_:
{
size_t v___x_2050_; size_t v___x_2051_; 
v___x_2050_ = ((size_t)1ULL);
v___x_2051_ = lean_usize_add(v_i_2035_, v___x_2050_);
v_i_2035_ = v___x_2051_;
v_b_2036_ = v_a_2049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2165_ = _args[0];
lean_object* v_lams_u2081_2166_ = _args[1];
lean_object* v_as_2167_ = _args[2];
lean_object* v_sz_2168_ = _args[3];
lean_object* v_i_2169_ = _args[4];
lean_object* v_b_2170_ = _args[5];
lean_object* v___y_2171_ = _args[6];
lean_object* v___y_2172_ = _args[7];
lean_object* v___y_2173_ = _args[8];
lean_object* v___y_2174_ = _args[9];
lean_object* v___y_2175_ = _args[10];
lean_object* v___y_2176_ = _args[11];
lean_object* v___y_2177_ = _args[12];
lean_object* v___y_2178_ = _args[13];
lean_object* v___y_2179_ = _args[14];
lean_object* v___y_2180_ = _args[15];
lean_object* v___y_2181_ = _args[16];
_start:
{
size_t v_sz_boxed_2182_; size_t v_i_boxed_2183_; lean_object* v_res_2184_; 
v_sz_boxed_2182_ = lean_unbox_usize(v_sz_2168_);
lean_dec(v_sz_2168_);
v_i_boxed_2183_ = lean_unbox_usize(v_i_2169_);
lean_dec(v_i_2169_);
v_res_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2165_, v_lams_u2081_2166_, v_as_2167_, v_sz_boxed_2182_, v_i_boxed_2183_, v_b_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v_as_2167_);
lean_dec_ref(v_lams_u2081_2166_);
lean_dec_ref(v_lams_u2082_2165_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2185_, lean_object* v_lams_u2082_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_array_get_size(v_lams_u2081_2185_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = lean_array_get_size(v_lams_u2082_2186_);
v___x_2202_ = lean_nat_dec_eq(v___x_2201_, v___x_2199_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; size_t v_sz_2204_; size_t v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = lean_box(0);
v_sz_2204_ = lean_array_size(v_lams_u2081_2185_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2186_, v_lams_u2081_2185_, v_lams_u2081_2185_, v_sz_2204_, v___x_2205_, v___x_2203_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v___x_2206_, 0);
lean_dec(v_unused_2214_);
v___x_2208_ = v___x_2206_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v___x_2206_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2203_);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2203_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
return v___x_2206_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2219_, lean_object* v_lams_u2082_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2219_, v_lams_u2082_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_lams_u2082_2220_);
lean_dec_ref(v_lams_u2081_2219_);
return v_res_2232_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2233_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2235_){
_start:
{
uint8_t v_res_2236_; lean_object* v_r_2237_; 
v_res_2236_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2235_);
lean_dec_ref(v_x_2235_);
v_r_2237_ = lean_box(v_res_2236_);
return v_r_2237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2238_, lean_object* v_x_2239_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2241_, lean_object* v_x_2242_){
_start:
{
uint8_t v_res_2243_; lean_object* v_r_2244_; 
v_res_2243_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2241_, v_x_2242_);
lean_dec_ref(v_x_2242_);
v_r_2244_ = lean_box(v_res_2243_);
return v_r_2244_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2245_, lean_object* v_v_2246_, lean_object* v_i_2247_){
_start:
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = lean_array_get_size(v_xs_2245_);
v___x_2249_ = lean_nat_dec_lt(v_i_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_i_2247_);
v___x_2250_ = lean_box(0);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; uint8_t v___x_2254_; 
v___x_2251_ = lean_array_fget_borrowed(v_xs_2245_, v_i_2247_);
v___x_2252_ = lean_ptr_addr(v___x_2251_);
v___x_2253_ = lean_ptr_addr(v_v_2246_);
v___x_2254_ = lean_usize_dec_eq(v___x_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_nat_add(v_i_2247_, v___x_2255_);
lean_dec(v_i_2247_);
v_i_2247_ = v___x_2256_;
goto _start;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_i_2247_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2259_, lean_object* v_v_2260_, lean_object* v_i_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2259_, v_v_2260_, v_i_2261_);
lean_dec_ref(v_v_2260_);
lean_dec_ref(v_xs_2259_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2263_, lean_object* v_v_2264_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2263_, v_v_2264_, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2267_, lean_object* v_v_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2267_, v_v_2268_);
lean_dec_ref(v_v_2268_);
lean_dec_ref(v_xs_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2270_, size_t v_x_2271_, lean_object* v_x_2272_){
_start:
{
if (lean_obj_tag(v_x_2270_) == 0)
{
lean_object* v_es_2273_; lean_object* v___x_2274_; size_t v___x_2275_; size_t v___x_2276_; lean_object* v_j_2277_; lean_object* v_entry_2278_; 
v_es_2273_ = lean_ctor_get(v_x_2270_, 0);
v___x_2274_ = lean_box(2);
v___x_2275_ = ((size_t)31ULL);
v___x_2276_ = lean_usize_land(v_x_2271_, v___x_2275_);
v_j_2277_ = lean_usize_to_nat(v___x_2276_);
v_entry_2278_ = lean_array_get(v___x_2274_, v_es_2273_, v_j_2277_);
switch(lean_obj_tag(v_entry_2278_))
{
case 0:
{
lean_object* v_key_2279_; size_t v___x_2280_; size_t v___x_2281_; uint8_t v___x_2282_; 
v_key_2279_ = lean_ctor_get(v_entry_2278_, 0);
lean_inc(v_key_2279_);
lean_dec_ref_known(v_entry_2278_, 2);
v___x_2280_ = lean_ptr_addr(v_x_2272_);
v___x_2281_ = lean_ptr_addr(v_key_2279_);
lean_dec(v_key_2279_);
v___x_2282_ = lean_usize_dec_eq(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v_j_2277_);
return v_x_2270_;
}
else
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
lean_inc_ref(v_es_2273_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2270_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v_x_2270_, 0);
lean_dec(v_unused_2291_);
v___x_2284_ = v_x_2270_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_x_2270_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_array_set(v_es_2273_, v_j_2277_, v___x_2274_);
lean_dec(v_j_2277_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
case 1:
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2326_; 
lean_inc_ref(v_es_2273_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_x_2270_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_x_2270_, 0);
lean_dec(v_unused_2327_);
v___x_2293_ = v_x_2270_;
v_isShared_2294_ = v_isSharedCheck_2326_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v_x_2270_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2326_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_node_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2325_; 
v_node_2295_ = lean_ctor_get(v_entry_2278_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_entry_2278_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2297_ = v_entry_2278_;
v_isShared_2298_ = v_isSharedCheck_2325_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_node_2295_);
lean_dec(v_entry_2278_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2325_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
size_t v___x_2299_; lean_object* v_entries_2300_; size_t v___x_2301_; lean_object* v_newNode_2302_; lean_object* v___x_2303_; 
v___x_2299_ = ((size_t)5ULL);
v_entries_2300_ = lean_array_set(v_es_2273_, v_j_2277_, v___x_2274_);
v___x_2301_ = lean_usize_shift_right(v_x_2271_, v___x_2299_);
v_newNode_2302_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2295_, v___x_2301_, v_x_2272_);
lean_inc_ref(v_newNode_2302_);
v___x_2303_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2305_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_newNode_2302_);
v___x_2305_ = v___x_2297_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_newNode_2302_);
v___x_2305_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_array_set(v_entries_2300_, v_j_2277_, v___x_2305_);
lean_dec(v_j_2277_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2306_);
v___x_2308_ = v___x_2293_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_object* v_val_2311_; lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_newNode_2302_);
lean_del_object(v___x_2297_);
v_val_2311_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2311_);
lean_dec_ref_known(v___x_2303_, 1);
v_fst_2312_ = lean_ctor_get(v_val_2311_, 0);
v_snd_2313_ = lean_ctor_get(v_val_2311_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_val_2311_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2315_ = v_val_2311_;
v_isShared_2316_ = v_isSharedCheck_2324_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snd_2313_);
lean_inc(v_fst_2312_);
lean_dec(v_val_2311_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2324_;
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
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2312_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_snd_2313_);
v___x_2318_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_array_set(v_entries_2300_, v_j_2277_, v___x_2318_);
lean_dec(v_j_2277_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2319_);
v___x_2321_ = v___x_2293_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2277_);
return v_x_2270_;
}
}
}
else
{
lean_object* v_ks_2328_; lean_object* v_vs_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2343_; 
v_ks_2328_ = lean_ctor_get(v_x_2270_, 0);
v_vs_2329_ = lean_ctor_get(v_x_2270_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_x_2270_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2331_ = v_x_2270_;
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_vs_2329_);
lean_inc(v_ks_2328_);
lean_dec(v_x_2270_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2328_, v_x_2272_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2335_; 
if (v_isShared_2332_ == 0)
{
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_ks_2328_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_vs_2329_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
else
{
lean_object* v_val_2337_; lean_object* v_keys_x27_2338_; lean_object* v_vals_x27_2339_; lean_object* v___x_2341_; 
v_val_2337_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_n(v_val_2337_, 2);
lean_dec_ref_known(v___x_2333_, 1);
v_keys_x27_2338_ = l_Array_eraseIdx___redArg(v_ks_2328_, v_val_2337_);
v_vals_x27_2339_ = l_Array_eraseIdx___redArg(v_vs_2329_, v_val_2337_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v_vals_x27_2339_);
lean_ctor_set(v___x_2331_, 0, v_keys_x27_2338_);
v___x_2341_ = v___x_2331_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_keys_x27_2338_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_vals_x27_2339_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v_x_19465__boxed_2347_; lean_object* v_res_2348_; 
v_x_19465__boxed_2347_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_res_2348_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2344_, v_x_19465__boxed_2347_, v_x_2346_);
lean_dec_ref(v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
size_t v___x_2351_; size_t v___x_2352_; size_t v___x_2353_; uint64_t v___x_2354_; size_t v_h_2355_; lean_object* v___x_2356_; 
v___x_2351_ = lean_ptr_addr(v_x_2350_);
v___x_2352_ = ((size_t)3ULL);
v___x_2353_ = lean_usize_shift_right(v___x_2351_, v___x_2352_);
v___x_2354_ = lean_usize_to_uint64(v___x_2353_);
v_h_2355_ = lean_uint64_to_usize(v___x_2354_);
v___x_2356_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2349_, v_h_2355_, v_x_2350_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2357_, v_x_2358_);
lean_dec_ref(v_x_2358_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
if (lean_obj_tag(v_as_2360_) == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
else
{
lean_object* v_head_2374_; lean_object* v_tail_2375_; lean_object* v___x_2376_; 
v_head_2374_ = lean_ctor_get(v_as_2360_, 0);
lean_inc(v_head_2374_);
v_tail_2375_ = lean_ctor_get(v_as_2360_, 1);
lean_inc(v_tail_2375_);
lean_dec_ref_known(v_as_2360_, 2);
v___x_2376_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2374_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_dec_ref_known(v___x_2376_, 1);
v_as_2360_ = v_tail_2375_;
goto _start;
}
else
{
lean_dec(v_tail_2375_);
return v___x_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec(v___y_2379_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2391_, lean_object* v_vals_2392_, lean_object* v_i_2393_, lean_object* v_k_2394_){
_start:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_array_get_size(v_keys_2391_);
v___x_2396_ = lean_nat_dec_lt(v_i_2393_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec(v_i_2393_);
v___x_2397_ = lean_box(0);
return v___x_2397_;
}
else
{
lean_object* v_k_x27_2398_; size_t v___x_2399_; size_t v___x_2400_; uint8_t v___x_2401_; 
v_k_x27_2398_ = lean_array_fget_borrowed(v_keys_2391_, v_i_2393_);
v___x_2399_ = lean_ptr_addr(v_k_2394_);
v___x_2400_ = lean_ptr_addr(v_k_x27_2398_);
v___x_2401_ = lean_usize_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_add(v_i_2393_, v___x_2402_);
lean_dec(v_i_2393_);
v_i_2393_ = v___x_2403_;
goto _start;
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_array_fget_borrowed(v_vals_2392_, v_i_2393_);
lean_dec(v_i_2393_);
lean_inc(v___x_2405_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2407_, lean_object* v_vals_2408_, lean_object* v_i_2409_, lean_object* v_k_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2407_, v_vals_2408_, v_i_2409_, v_k_2410_);
lean_dec_ref(v_k_2410_);
lean_dec_ref(v_vals_2408_);
lean_dec_ref(v_keys_2407_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2412_, size_t v_x_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2412_) == 0)
{
lean_object* v_es_2415_; lean_object* v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v_j_2419_; lean_object* v___x_2420_; 
v_es_2415_ = lean_ctor_get(v_x_2412_, 0);
v___x_2416_ = lean_box(2);
v___x_2417_ = ((size_t)31ULL);
v___x_2418_ = lean_usize_land(v_x_2413_, v___x_2417_);
v_j_2419_ = lean_usize_to_nat(v___x_2418_);
v___x_2420_ = lean_array_get_borrowed(v___x_2416_, v_es_2415_, v_j_2419_);
lean_dec(v_j_2419_);
switch(lean_obj_tag(v___x_2420_))
{
case 0:
{
lean_object* v_key_2421_; lean_object* v_val_2422_; size_t v___x_2423_; size_t v___x_2424_; uint8_t v___x_2425_; 
v_key_2421_ = lean_ctor_get(v___x_2420_, 0);
v_val_2422_ = lean_ctor_get(v___x_2420_, 1);
v___x_2423_ = lean_ptr_addr(v_x_2414_);
v___x_2424_ = lean_ptr_addr(v_key_2421_);
v___x_2425_ = lean_usize_dec_eq(v___x_2423_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; 
lean_inc(v_val_2422_);
v___x_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_val_2422_);
return v___x_2427_;
}
}
case 1:
{
lean_object* v_node_2428_; size_t v___x_2429_; size_t v___x_2430_; 
v_node_2428_ = lean_ctor_get(v___x_2420_, 0);
v___x_2429_ = ((size_t)5ULL);
v___x_2430_ = lean_usize_shift_right(v_x_2413_, v___x_2429_);
v_x_2412_ = v_node_2428_;
v_x_2413_ = v___x_2430_;
goto _start;
}
default: 
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_box(0);
return v___x_2432_;
}
}
}
else
{
lean_object* v_ks_2433_; lean_object* v_vs_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_ks_2433_ = lean_ctor_get(v_x_2412_, 0);
v_vs_2434_ = lean_ctor_get(v_x_2412_, 1);
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2433_, v_vs_2434_, v___x_2435_, v_x_2414_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
size_t v_x_19690__boxed_2440_; lean_object* v_res_2441_; 
v_x_19690__boxed_2440_ = lean_unbox_usize(v_x_2438_);
lean_dec(v_x_2438_);
v_res_2441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2437_, v_x_19690__boxed_2440_, v_x_2439_);
lean_dec_ref(v_x_2439_);
lean_dec_ref(v_x_2437_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; uint64_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = lean_ptr_addr(v_x_2443_);
v___x_2445_ = ((size_t)3ULL);
v___x_2446_ = lean_usize_shift_right(v___x_2444_, v___x_2445_);
v___x_2447_ = lean_usize_to_uint64(v___x_2446_);
v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
v___x_2449_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2442_, v___x_2448_, v_x_2443_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2450_, v_x_2451_);
lean_dec_ref(v_x_2451_);
lean_dec_ref(v_x_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
if (lean_obj_tag(v_as_x27_2453_) == 0)
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2466_, 0, v_b_2454_);
return v___x_2466_;
}
else
{
lean_object* v_head_2467_; lean_object* v_tail_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_toGoalState_2471_; lean_object* v_ematch_2472_; lean_object* v_delayedThmInsts_2473_; lean_object* v___x_2474_; 
v_head_2467_ = lean_ctor_get(v_as_x27_2453_, 0);
v_tail_2468_ = lean_ctor_get(v_as_x27_2453_, 1);
v___x_2469_ = lean_box(0);
v___x_2470_ = lean_st_ref_get(v___y_2455_);
v_toGoalState_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_ref(v_toGoalState_2471_);
lean_dec(v___x_2470_);
v_ematch_2472_ = lean_ctor_get(v_toGoalState_2471_, 13);
lean_inc_ref(v_ematch_2472_);
lean_dec_ref(v_toGoalState_2471_);
v_delayedThmInsts_2473_ = lean_ctor_get(v_ematch_2472_, 10);
lean_inc_ref(v_delayedThmInsts_2473_);
lean_dec_ref(v_ematch_2472_);
v___x_2474_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2473_, v_head_2467_);
lean_dec_ref(v_delayedThmInsts_2473_);
if (lean_obj_tag(v___x_2474_) == 1)
{
lean_object* v_val_2475_; lean_object* v___x_2476_; lean_object* v_toGoalState_2477_; lean_object* v_ematch_2478_; lean_object* v_mvarId_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2534_; 
v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = lean_st_ref_take(v___y_2455_);
v_toGoalState_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_toGoalState_2477_);
v_ematch_2478_ = lean_ctor_get(v_toGoalState_2477_, 13);
lean_inc_ref(v_ematch_2478_);
v_mvarId_2479_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2535_);
v___x_2481_ = v___x_2476_;
v_isShared_2482_ = v_isSharedCheck_2534_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_mvarId_2479_);
lean_dec(v___x_2476_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2534_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_nextDeclIdx_2483_; lean_object* v_enodeMap_2484_; lean_object* v_exprs_2485_; lean_object* v_parents_2486_; lean_object* v_congrTable_2487_; lean_object* v_appMap_2488_; lean_object* v_indicesFound_2489_; lean_object* v_toProcess_2490_; lean_object* v_internalizing_2491_; uint8_t v_inconsistent_2492_; lean_object* v_nextIdx_2493_; lean_object* v_newRawFacts_2494_; lean_object* v_facts_2495_; lean_object* v_extThms_2496_; lean_object* v_inj_2497_; lean_object* v_split_2498_; lean_object* v_clean_2499_; lean_object* v_sstates_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2532_; 
v_nextDeclIdx_2483_ = lean_ctor_get(v_toGoalState_2477_, 0);
v_enodeMap_2484_ = lean_ctor_get(v_toGoalState_2477_, 1);
v_exprs_2485_ = lean_ctor_get(v_toGoalState_2477_, 2);
v_parents_2486_ = lean_ctor_get(v_toGoalState_2477_, 3);
v_congrTable_2487_ = lean_ctor_get(v_toGoalState_2477_, 4);
v_appMap_2488_ = lean_ctor_get(v_toGoalState_2477_, 5);
v_indicesFound_2489_ = lean_ctor_get(v_toGoalState_2477_, 6);
v_toProcess_2490_ = lean_ctor_get(v_toGoalState_2477_, 7);
v_internalizing_2491_ = lean_ctor_get(v_toGoalState_2477_, 8);
v_inconsistent_2492_ = lean_ctor_get_uint8(v_toGoalState_2477_, sizeof(void*)*18);
v_nextIdx_2493_ = lean_ctor_get(v_toGoalState_2477_, 9);
v_newRawFacts_2494_ = lean_ctor_get(v_toGoalState_2477_, 10);
v_facts_2495_ = lean_ctor_get(v_toGoalState_2477_, 11);
v_extThms_2496_ = lean_ctor_get(v_toGoalState_2477_, 12);
v_inj_2497_ = lean_ctor_get(v_toGoalState_2477_, 14);
v_split_2498_ = lean_ctor_get(v_toGoalState_2477_, 15);
v_clean_2499_ = lean_ctor_get(v_toGoalState_2477_, 16);
v_sstates_2500_ = lean_ctor_get(v_toGoalState_2477_, 17);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_toGoalState_2477_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v_toGoalState_2477_, 13);
lean_dec(v_unused_2533_);
v___x_2502_ = v_toGoalState_2477_;
v_isShared_2503_ = v_isSharedCheck_2532_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_sstates_2500_);
lean_inc(v_clean_2499_);
lean_inc(v_split_2498_);
lean_inc(v_inj_2497_);
lean_inc(v_extThms_2496_);
lean_inc(v_facts_2495_);
lean_inc(v_newRawFacts_2494_);
lean_inc(v_nextIdx_2493_);
lean_inc(v_internalizing_2491_);
lean_inc(v_toProcess_2490_);
lean_inc(v_indicesFound_2489_);
lean_inc(v_appMap_2488_);
lean_inc(v_congrTable_2487_);
lean_inc(v_parents_2486_);
lean_inc(v_exprs_2485_);
lean_inc(v_enodeMap_2484_);
lean_inc(v_nextDeclIdx_2483_);
lean_dec(v_toGoalState_2477_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2532_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_thmMap_2504_; lean_object* v_gmt_2505_; lean_object* v_thms_2506_; lean_object* v_newThms_2507_; lean_object* v_numInstances_2508_; lean_object* v_numDelayedInstances_2509_; lean_object* v_num_2510_; lean_object* v_preInstances_2511_; lean_object* v_nextThmIdx_2512_; lean_object* v_matchEqNames_2513_; lean_object* v_delayedThmInsts_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2531_; 
v_thmMap_2504_ = lean_ctor_get(v_ematch_2478_, 0);
v_gmt_2505_ = lean_ctor_get(v_ematch_2478_, 1);
v_thms_2506_ = lean_ctor_get(v_ematch_2478_, 2);
v_newThms_2507_ = lean_ctor_get(v_ematch_2478_, 3);
v_numInstances_2508_ = lean_ctor_get(v_ematch_2478_, 4);
v_numDelayedInstances_2509_ = lean_ctor_get(v_ematch_2478_, 5);
v_num_2510_ = lean_ctor_get(v_ematch_2478_, 6);
v_preInstances_2511_ = lean_ctor_get(v_ematch_2478_, 7);
v_nextThmIdx_2512_ = lean_ctor_get(v_ematch_2478_, 8);
v_matchEqNames_2513_ = lean_ctor_get(v_ematch_2478_, 9);
v_delayedThmInsts_2514_ = lean_ctor_get(v_ematch_2478_, 10);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_ematch_2478_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2516_ = v_ematch_2478_;
v_isShared_2517_ = v_isSharedCheck_2531_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_delayedThmInsts_2514_);
lean_inc(v_matchEqNames_2513_);
lean_inc(v_nextThmIdx_2512_);
lean_inc(v_preInstances_2511_);
lean_inc(v_num_2510_);
lean_inc(v_numDelayedInstances_2509_);
lean_inc(v_numInstances_2508_);
lean_inc(v_newThms_2507_);
lean_inc(v_thms_2506_);
lean_inc(v_gmt_2505_);
lean_inc(v_thmMap_2504_);
lean_dec(v_ematch_2478_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2531_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2514_, v_head_2467_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 10, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_thmMap_2504_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_gmt_2505_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_thms_2506_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_newThms_2507_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_numInstances_2508_);
lean_ctor_set(v_reuseFailAlloc_2530_, 5, v_numDelayedInstances_2509_);
lean_ctor_set(v_reuseFailAlloc_2530_, 6, v_num_2510_);
lean_ctor_set(v_reuseFailAlloc_2530_, 7, v_preInstances_2511_);
lean_ctor_set(v_reuseFailAlloc_2530_, 8, v_nextThmIdx_2512_);
lean_ctor_set(v_reuseFailAlloc_2530_, 9, v_matchEqNames_2513_);
lean_ctor_set(v_reuseFailAlloc_2530_, 10, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 13, v___x_2520_);
v___x_2522_ = v___x_2502_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_nextDeclIdx_2483_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_enodeMap_2484_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_exprs_2485_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_parents_2486_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_congrTable_2487_);
lean_ctor_set(v_reuseFailAlloc_2529_, 5, v_appMap_2488_);
lean_ctor_set(v_reuseFailAlloc_2529_, 6, v_indicesFound_2489_);
lean_ctor_set(v_reuseFailAlloc_2529_, 7, v_toProcess_2490_);
lean_ctor_set(v_reuseFailAlloc_2529_, 8, v_internalizing_2491_);
lean_ctor_set(v_reuseFailAlloc_2529_, 9, v_nextIdx_2493_);
lean_ctor_set(v_reuseFailAlloc_2529_, 10, v_newRawFacts_2494_);
lean_ctor_set(v_reuseFailAlloc_2529_, 11, v_facts_2495_);
lean_ctor_set(v_reuseFailAlloc_2529_, 12, v_extThms_2496_);
lean_ctor_set(v_reuseFailAlloc_2529_, 13, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2529_, 14, v_inj_2497_);
lean_ctor_set(v_reuseFailAlloc_2529_, 15, v_split_2498_);
lean_ctor_set(v_reuseFailAlloc_2529_, 16, v_clean_2499_);
lean_ctor_set(v_reuseFailAlloc_2529_, 17, v_sstates_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2529_, sizeof(void*)*18, v_inconsistent_2492_);
v___x_2522_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2522_);
v___x_2524_ = v___x_2481_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_mvarId_2479_);
v___x_2524_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_st_ref_put(v___y_2455_, v___x_2524_);
v___x_2526_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2475_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_dec_ref_known(v___x_2526_, 1);
v_as_x27_2453_ = v_tail_2468_;
v_b_2454_ = v___x_2469_;
goto _start;
}
else
{
return v___x_2526_;
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
lean_dec(v___x_2474_);
v_as_x27_2453_ = v_tail_2468_;
v_b_2454_ = v___x_2469_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2537_, v_b_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec(v_as_x27_2537_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2552_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2592_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2592_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2592_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_unbox(v_a_2564_);
lean_dec(v_a_2564_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v_toGoalState_2570_; lean_object* v_ematch_2571_; lean_object* v_delayedThmInsts_2572_; uint8_t v___x_2573_; 
v___x_2569_ = lean_st_ref_get(v_a_2552_);
v_toGoalState_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_toGoalState_2570_);
lean_dec(v___x_2569_);
v_ematch_2571_ = lean_ctor_get(v_toGoalState_2570_, 13);
lean_inc_ref(v_ematch_2571_);
lean_dec_ref(v_toGoalState_2570_);
v_delayedThmInsts_2572_ = lean_ctor_get(v_ematch_2571_, 10);
lean_inc_ref(v_delayedThmInsts_2572_);
lean_dec_ref(v_ematch_2571_);
v___x_2573_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2572_);
lean_dec_ref(v_delayedThmInsts_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_del_object(v___x_2566_);
v___x_2574_ = lean_box(0);
v___x_2575_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2551_, v___x_2574_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2583_);
v___x_2577_ = v___x_2575_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_dec(v___x_2575_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2574_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2574_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
else
{
return v___x_2575_;
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_box(0);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2584_);
v___x_2586_ = v___x_2566_;
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
else
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2588_);
v___x_2590_ = v___x_2566_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
v_a_2593_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2563_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2563_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec(v_a_2602_);
lean_dec(v_toPropagateDown_2601_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2618_, v_x_2619_, v_x_2620_);
lean_dec_ref(v_x_2620_);
lean_dec_ref(v_x_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2622_, lean_object* v_x_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2623_, v_x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2626_, v_x_2627_, v_x_2628_);
lean_dec_ref(v_x_2628_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2630_, lean_object* v_as_x27_2631_, lean_object* v_b_2632_, lean_object* v_a_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2631_, v_b_2632_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2646_, lean_object* v_as_x27_2647_, lean_object* v_b_2648_, lean_object* v_a_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2646_, v_as_x27_2647_, v_b_2648_, v_a_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec(v_as_x27_2647_);
lean_dec(v_as_2646_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2662_, lean_object* v_x_2663_, size_t v_x_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2663_, v_x_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_, lean_object* v_x_2670_){
_start:
{
size_t v_x_19995__boxed_2671_; lean_object* v_res_2672_; 
v_x_19995__boxed_2671_ = lean_unbox_usize(v_x_2669_);
lean_dec(v_x_2669_);
v_res_2672_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2667_, v_x_2668_, v_x_19995__boxed_2671_, v_x_2670_);
lean_dec_ref(v_x_2670_);
lean_dec_ref(v_x_2668_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2673_, lean_object* v_x_2674_, size_t v_x_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2674_, v_x_2675_, v_x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_){
_start:
{
size_t v_x_20006__boxed_2682_; lean_object* v_res_2683_; 
v_x_20006__boxed_2682_ = lean_unbox_usize(v_x_2680_);
lean_dec(v_x_2680_);
v_res_2683_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2678_, v_x_2679_, v_x_20006__boxed_2682_, v_x_2681_);
lean_dec_ref(v_x_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2684_, lean_object* v_keys_2685_, lean_object* v_vals_2686_, lean_object* v_heq_2687_, lean_object* v_i_2688_, lean_object* v_k_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2685_, v_vals_2686_, v_i_2688_, v_k_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2691_, lean_object* v_keys_2692_, lean_object* v_vals_2693_, lean_object* v_heq_2694_, lean_object* v_i_2695_, lean_object* v_k_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2691_, v_keys_2692_, v_vals_2693_, v_heq_2694_, v_i_2695_, v_k_2696_);
lean_dec_ref(v_k_2696_);
lean_dec_ref(v_vals_2693_);
lean_dec_ref(v_keys_2692_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2698_, lean_object* v_keys_2699_, lean_object* v_vals_2700_, lean_object* v_i_2701_, lean_object* v_k_2702_){
_start:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = lean_array_get_size(v_keys_2699_);
v___x_2704_ = lean_nat_dec_lt(v_i_2701_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec_ref(v_k_2702_);
lean_dec(v_i_2701_);
v___x_2705_ = lean_box(0);
return v___x_2705_;
}
else
{
lean_object* v_k_x27_2706_; uint8_t v___x_2707_; 
v_k_x27_2706_ = lean_array_fget_borrowed(v_keys_2699_, v_i_2701_);
lean_inc(v_k_x27_2706_);
lean_inc_ref(v_k_2702_);
v___x_2707_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2698_, v_k_2702_, v_k_x27_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_add(v_i_2701_, v___x_2708_);
lean_dec(v_i_2701_);
v_i_2701_ = v___x_2709_;
goto _start;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec_ref(v_k_2702_);
v___x_2711_ = lean_array_fget_borrowed(v_vals_2700_, v_i_2701_);
lean_dec(v_i_2701_);
lean_inc(v___x_2711_);
lean_inc(v_k_x27_2706_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_k_x27_2706_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
return v___x_2713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2714_, lean_object* v_keys_2715_, lean_object* v_vals_2716_, lean_object* v_i_2717_, lean_object* v_k_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2714_, v_keys_2715_, v_vals_2716_, v_i_2717_, v_k_2718_);
lean_dec_ref(v_vals_2716_);
lean_dec_ref(v_keys_2715_);
lean_dec_ref(v___x_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2720_, lean_object* v_x_2721_, size_t v_x_2722_, lean_object* v_x_2723_){
_start:
{
if (lean_obj_tag(v_x_2721_) == 0)
{
lean_object* v_es_2724_; lean_object* v___x_2725_; size_t v___x_2726_; size_t v___x_2727_; lean_object* v_j_2728_; lean_object* v___x_2729_; 
v_es_2724_ = lean_ctor_get(v_x_2721_, 0);
lean_inc_ref(v_es_2724_);
lean_dec_ref_known(v_x_2721_, 1);
v___x_2725_ = lean_box(2);
v___x_2726_ = ((size_t)31ULL);
v___x_2727_ = lean_usize_land(v_x_2722_, v___x_2726_);
v_j_2728_ = lean_usize_to_nat(v___x_2727_);
v___x_2729_ = lean_array_get(v___x_2725_, v_es_2724_, v_j_2728_);
lean_dec(v_j_2728_);
lean_dec_ref(v_es_2724_);
switch(lean_obj_tag(v___x_2729_))
{
case 0:
{
lean_object* v_key_2730_; lean_object* v_val_2731_; uint8_t v___x_2732_; 
v_key_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_n(v_key_2730_, 2);
v_val_2731_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_val_2731_);
lean_dec_ref_known(v___x_2729_, 2);
v___x_2732_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2720_, v_x_2723_, v_key_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
lean_dec(v_val_2731_);
lean_dec(v_key_2730_);
v___x_2733_ = lean_box(0);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_key_2730_);
lean_ctor_set(v___x_2734_, 1, v_val_2731_);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
case 1:
{
lean_object* v_node_2736_; size_t v___x_2737_; size_t v___x_2738_; 
v_node_2736_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_node_2736_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2737_ = ((size_t)5ULL);
v___x_2738_ = lean_usize_shift_right(v_x_2722_, v___x_2737_);
v_x_2721_ = v_node_2736_;
v_x_2722_ = v___x_2738_;
goto _start;
}
default: 
{
lean_object* v___x_2740_; 
lean_dec_ref(v_x_2723_);
v___x_2740_ = lean_box(0);
return v___x_2740_;
}
}
}
else
{
lean_object* v_ks_2741_; lean_object* v_vs_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v_ks_2741_ = lean_ctor_get(v_x_2721_, 0);
lean_inc_ref(v_ks_2741_);
v_vs_2742_ = lean_ctor_get(v_x_2721_, 1);
lean_inc_ref(v_vs_2742_);
lean_dec_ref_known(v_x_2721_, 2);
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2720_, v_ks_2741_, v_vs_2742_, v___x_2743_, v_x_2723_);
lean_dec_ref(v_vs_2742_);
lean_dec_ref(v_ks_2741_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
size_t v_x_26075__boxed_2749_; lean_object* v_res_2750_; 
v_x_26075__boxed_2749_ = lean_unbox_usize(v_x_2747_);
lean_dec(v_x_2747_);
v_res_2750_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2745_, v_x_2746_, v_x_26075__boxed_2749_, v_x_2748_);
lean_dec_ref(v___x_2745_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
uint64_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
lean_inc_ref(v_x_2753_);
v___x_2754_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2751_, v_x_2753_);
v___x_2755_ = lean_uint64_to_usize(v___x_2754_);
lean_inc_ref(v_x_2752_);
v___x_2756_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2751_, v_x_2752_, v___x_2755_, v_x_2753_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2757_, v_x_2758_, v_x_2759_);
lean_dec_ref(v_x_2758_);
lean_dec_ref(v___x_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v_ks_2766_; lean_object* v_vs_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2791_; 
v_ks_2766_ = lean_ctor_get(v_x_2762_, 0);
v_vs_2767_ = lean_ctor_get(v_x_2762_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_x_2762_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2769_ = v_x_2762_;
v_isShared_2770_ = v_isSharedCheck_2791_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_vs_2767_);
lean_inc(v_ks_2766_);
lean_dec(v_x_2762_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2791_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = lean_array_get_size(v_ks_2766_);
v___x_2772_ = lean_nat_dec_lt(v_x_2763_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
lean_dec(v_x_2763_);
v___x_2773_ = lean_array_push(v_ks_2766_, v_x_2764_);
v___x_2774_ = lean_array_push(v_vs_2767_, v_x_2765_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2774_);
lean_ctor_set(v___x_2769_, 0, v___x_2773_);
v___x_2776_ = v___x_2769_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
else
{
lean_object* v_k_x27_2778_; uint8_t v___x_2779_; 
v_k_x27_2778_ = lean_array_fget_borrowed(v_ks_2766_, v_x_2763_);
lean_inc(v_k_x27_2778_);
lean_inc_ref(v_x_2764_);
v___x_2779_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2761_, v_x_2764_, v_k_x27_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2781_; 
if (v_isShared_2770_ == 0)
{
v___x_2781_ = v___x_2769_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_ks_2766_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_vs_2767_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_add(v_x_2763_, v___x_2782_);
lean_dec(v_x_2763_);
v_x_2762_ = v___x_2781_;
v_x_2763_ = v___x_2783_;
goto _start;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = lean_array_fset(v_ks_2766_, v_x_2763_, v_x_2764_);
v___x_2787_ = lean_array_fset(v_vs_2767_, v_x_2763_, v_x_2765_);
lean_dec(v_x_2763_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2787_);
lean_ctor_set(v___x_2769_, 0, v___x_2786_);
v___x_2789_ = v___x_2769_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2792_, v_x_2793_, v_x_2794_, v_x_2795_, v_x_2796_);
lean_dec_ref(v___x_2792_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2798_, lean_object* v_n_2799_, lean_object* v_k_2800_, lean_object* v_v_2801_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2798_, v_n_2799_, v___x_2802_, v_k_2800_, v_v_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2804_, lean_object* v_n_2805_, lean_object* v_k_2806_, lean_object* v_v_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2804_, v_n_2805_, v_k_2806_, v_v_2807_);
lean_dec_ref(v___x_2804_);
return v_res_2808_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2810_, lean_object* v_x_2811_, size_t v_x_2812_, size_t v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_){
_start:
{
if (lean_obj_tag(v_x_2811_) == 0)
{
lean_object* v_es_2816_; size_t v___x_2817_; size_t v___x_2818_; lean_object* v_j_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v_es_2816_ = lean_ctor_get(v_x_2811_, 0);
v___x_2817_ = ((size_t)31ULL);
v___x_2818_ = lean_usize_land(v_x_2812_, v___x_2817_);
v_j_2819_ = lean_usize_to_nat(v___x_2818_);
v___x_2820_ = lean_array_get_size(v_es_2816_);
v___x_2821_ = lean_nat_dec_lt(v_j_2819_, v___x_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_j_2819_);
lean_dec(v_x_2815_);
lean_dec_ref(v_x_2814_);
return v_x_2811_;
}
else
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2860_; 
lean_inc_ref(v_es_2816_);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_x_2811_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v_x_2811_, 0);
lean_dec(v_unused_2861_);
v___x_2823_ = v_x_2811_;
v_isShared_2824_ = v_isSharedCheck_2860_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v_x_2811_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2860_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_v_2825_; lean_object* v___x_2826_; lean_object* v_xs_x27_2827_; lean_object* v___y_2829_; 
v_v_2825_ = lean_array_fget(v_es_2816_, v_j_2819_);
v___x_2826_ = lean_box(0);
v_xs_x27_2827_ = lean_array_fset(v_es_2816_, v_j_2819_, v___x_2826_);
switch(lean_obj_tag(v_v_2825_))
{
case 0:
{
lean_object* v_key_2834_; lean_object* v_val_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2845_; 
v_key_2834_ = lean_ctor_get(v_v_2825_, 0);
v_val_2835_ = lean_ctor_get(v_v_2825_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_v_2825_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2837_ = v_v_2825_;
v_isShared_2838_ = v_isSharedCheck_2845_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_val_2835_);
lean_inc(v_key_2834_);
lean_dec(v_v_2825_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2845_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint8_t v___x_2839_; 
lean_inc(v_key_2834_);
lean_inc_ref(v_x_2814_);
v___x_2839_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2810_, v_x_2814_, v_key_2834_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2837_);
v___x_2840_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2834_, v_val_2835_, v_x_2814_, v_x_2815_);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
v___y_2829_ = v___x_2841_;
goto v___jp_2828_;
}
else
{
lean_object* v___x_2843_; 
lean_dec(v_val_2835_);
lean_dec(v_key_2834_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_x_2815_);
lean_ctor_set(v___x_2837_, 0, v_x_2814_);
v___x_2843_ = v___x_2837_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_x_2814_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_x_2815_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
v___y_2829_ = v___x_2843_;
goto v___jp_2828_;
}
}
}
}
case 1:
{
lean_object* v_node_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2858_; 
v_node_2846_ = lean_ctor_get(v_v_2825_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_v_2825_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2848_ = v_v_2825_;
v_isShared_2849_ = v_isSharedCheck_2858_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_node_2846_);
lean_dec(v_v_2825_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2858_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2850_ = ((size_t)5ULL);
v___x_2851_ = lean_usize_shift_right(v_x_2812_, v___x_2850_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_add(v_x_2813_, v___x_2852_);
v___x_2854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2810_, v_node_2846_, v___x_2851_, v___x_2853_, v_x_2814_, v_x_2815_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2854_);
v___x_2856_ = v___x_2848_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v___y_2829_ = v___x_2856_;
goto v___jp_2828_;
}
}
}
default: 
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_x_2814_);
lean_ctor_set(v___x_2859_, 1, v_x_2815_);
v___y_2829_ = v___x_2859_;
goto v___jp_2828_;
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = lean_array_fset(v_xs_x27_2827_, v_j_2819_, v___y_2829_);
lean_dec(v_j_2819_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2830_);
v___x_2832_ = v___x_2823_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
else
{
lean_object* v_ks_2862_; lean_object* v_vs_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2881_; 
v_ks_2862_ = lean_ctor_get(v_x_2811_, 0);
v_vs_2863_ = lean_ctor_get(v_x_2811_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2811_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2865_ = v_x_2811_;
v_isShared_2866_ = v_isSharedCheck_2881_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_vs_2863_);
lean_inc(v_ks_2862_);
lean_dec(v_x_2811_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2881_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_ks_2862_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_vs_2863_);
v___x_2868_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v_newNode_2869_; size_t v___x_2870_; uint8_t v___x_2871_; 
v_newNode_2869_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2810_, v___x_2868_, v_x_2814_, v_x_2815_);
v___x_2870_ = ((size_t)7ULL);
v___x_2871_ = lean_usize_dec_le(v___x_2870_, v_x_2813_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2869_);
v___x_2873_ = lean_unsigned_to_nat(4u);
v___x_2874_ = lean_nat_dec_lt(v___x_2872_, v___x_2873_);
lean_dec(v___x_2872_);
if (v___x_2874_ == 0)
{
lean_object* v_ks_2875_; lean_object* v_vs_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_ks_2875_ = lean_ctor_get(v_newNode_2869_, 0);
lean_inc_ref(v_ks_2875_);
v_vs_2876_ = lean_ctor_get(v_newNode_2869_, 1);
lean_inc_ref(v_vs_2876_);
lean_dec_ref(v_newNode_2869_);
v___x_2877_ = lean_unsigned_to_nat(0u);
v___x_2878_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2879_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2810_, v_x_2813_, v_ks_2875_, v_vs_2876_, v___x_2877_, v___x_2878_);
lean_dec_ref(v_vs_2876_);
lean_dec_ref(v_ks_2875_);
return v___x_2879_;
}
else
{
return v_newNode_2869_;
}
}
else
{
return v_newNode_2869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2882_, size_t v_depth_2883_, lean_object* v_keys_2884_, lean_object* v_vals_2885_, lean_object* v_i_2886_, lean_object* v_entries_2887_){
_start:
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = lean_array_get_size(v_keys_2884_);
v___x_2889_ = lean_nat_dec_lt(v_i_2886_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_dec(v_i_2886_);
return v_entries_2887_;
}
else
{
lean_object* v_k_2890_; lean_object* v_v_2891_; uint64_t v___x_2892_; size_t v_h_2893_; size_t v___x_2894_; lean_object* v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; size_t v_h_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_k_2890_ = lean_array_fget_borrowed(v_keys_2884_, v_i_2886_);
v_v_2891_ = lean_array_fget_borrowed(v_vals_2885_, v_i_2886_);
lean_inc_n(v_k_2890_, 2);
v___x_2892_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2882_, v_k_2890_);
v_h_2893_ = lean_uint64_to_usize(v___x_2892_);
v___x_2894_ = ((size_t)5ULL);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_sub(v_depth_2883_, v___x_2896_);
v___x_2898_ = lean_usize_mul(v___x_2894_, v___x_2897_);
v_h_2899_ = lean_usize_shift_right(v_h_2893_, v___x_2898_);
v___x_2900_ = lean_nat_add(v_i_2886_, v___x_2895_);
lean_dec(v_i_2886_);
lean_inc(v_v_2891_);
v___x_2901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2882_, v_entries_2887_, v_h_2899_, v_depth_2883_, v_k_2890_, v_v_2891_);
v_i_2886_ = v___x_2900_;
v_entries_2887_ = v___x_2901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2903_, lean_object* v_depth_2904_, lean_object* v_keys_2905_, lean_object* v_vals_2906_, lean_object* v_i_2907_, lean_object* v_entries_2908_){
_start:
{
size_t v_depth_boxed_2909_; lean_object* v_res_2910_; 
v_depth_boxed_2909_ = lean_unbox_usize(v_depth_2904_);
lean_dec(v_depth_2904_);
v_res_2910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2903_, v_depth_boxed_2909_, v_keys_2905_, v_vals_2906_, v_i_2907_, v_entries_2908_);
lean_dec_ref(v_vals_2906_);
lean_dec_ref(v_keys_2905_);
lean_dec_ref(v___x_2903_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
size_t v_x_26229__boxed_2917_; size_t v_x_26230__boxed_2918_; lean_object* v_res_2919_; 
v_x_26229__boxed_2917_ = lean_unbox_usize(v_x_2913_);
lean_dec(v_x_2913_);
v_x_26230__boxed_2918_ = lean_unbox_usize(v_x_2914_);
lean_dec(v_x_2914_);
v_res_2919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2911_, v_x_2912_, v_x_26229__boxed_2917_, v_x_26230__boxed_2918_, v_x_2915_, v_x_2916_);
lean_dec_ref(v___x_2911_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
uint64_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; 
lean_inc_ref(v_x_2922_);
v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2920_, v_x_2922_);
v___x_2925_ = lean_uint64_to_usize(v___x_2924_);
v___x_2926_ = ((size_t)1ULL);
v___x_2927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2920_, v_x_2921_, v___x_2925_, v___x_2926_, v_x_2922_, v_x_2923_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2928_, v_x_2929_, v_x_2930_, v_x_2931_);
lean_dec_ref(v___x_2928_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2937_, lean_object* v_rootNew_2938_, uint8_t v_a_2939_, lean_object* v_a_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_snd_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3119_; 
v_snd_2948_ = lean_ctor_get(v_a_2940_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_a_2940_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v_a_2940_, 0);
lean_dec(v_unused_3120_);
v___x_2950_ = v_a_2940_;
v_isShared_2951_ = v_isSharedCheck_3119_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_snd_2948_);
lean_dec(v_a_2940_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3119_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = lean_st_ref_get(v___y_2941_);
lean_inc(v_snd_2948_);
v___x_2954_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2953_, v_snd_2948_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___x_2953_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3110_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_3110_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3110_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_self_2959_; lean_object* v_next_2960_; lean_object* v_congr_2961_; lean_object* v_target_x3f_2962_; lean_object* v_proof_x3f_2963_; uint8_t v_flipped_2964_; lean_object* v_size_2965_; uint8_t v_interpreted_2966_; uint8_t v_ctor_2967_; uint8_t v_hasLambdas_2968_; uint8_t v_heqProofs_2969_; lean_object* v_idx_2970_; lean_object* v_generation_2971_; lean_object* v_mt_2972_; lean_object* v_sTerms_2973_; uint8_t v_funCC_2974_; lean_object* v_ematchDiagSource_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3108_; 
v_self_2959_ = lean_ctor_get(v_a_2955_, 0);
v_next_2960_ = lean_ctor_get(v_a_2955_, 1);
v_congr_2961_ = lean_ctor_get(v_a_2955_, 3);
v_target_x3f_2962_ = lean_ctor_get(v_a_2955_, 4);
v_proof_x3f_2963_ = lean_ctor_get(v_a_2955_, 5);
v_flipped_2964_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12);
v_size_2965_ = lean_ctor_get(v_a_2955_, 6);
v_interpreted_2966_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12 + 1);
v_ctor_2967_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12 + 2);
v_hasLambdas_2968_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12 + 3);
v_heqProofs_2969_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12 + 4);
v_idx_2970_ = lean_ctor_get(v_a_2955_, 7);
v_generation_2971_ = lean_ctor_get(v_a_2955_, 8);
v_mt_2972_ = lean_ctor_get(v_a_2955_, 9);
v_sTerms_2973_ = lean_ctor_get(v_a_2955_, 10);
v_funCC_2974_ = lean_ctor_get_uint8(v_a_2955_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2975_ = lean_ctor_get(v_a_2955_, 11);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_a_2955_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v_a_2955_, 2);
lean_dec(v_unused_3109_);
v___x_2977_ = v_a_2955_;
v_isShared_2978_ = v_isSharedCheck_3108_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_ematchDiagSource_2975_);
lean_inc(v_sTerms_2973_);
lean_inc(v_mt_2972_);
lean_inc(v_generation_2971_);
lean_inc(v_idx_2970_);
lean_inc(v_size_2965_);
lean_inc(v_proof_x3f_2963_);
lean_inc(v_target_x3f_2962_);
lean_inc(v_congr_2961_);
lean_inc(v_next_2960_);
lean_inc(v_self_2959_);
lean_dec(v_a_2955_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3108_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___y_2995_; lean_object* v___x_3005_; 
lean_inc(v_ematchDiagSource_2975_);
lean_inc(v_sTerms_2973_);
lean_inc(v_mt_2972_);
lean_inc(v_generation_2971_);
lean_inc(v_idx_2970_);
lean_inc(v_size_2965_);
lean_inc(v_proof_x3f_2963_);
lean_inc(v_target_x3f_2962_);
lean_inc_ref(v_rootNew_2938_);
lean_inc_ref(v_next_2960_);
lean_inc_ref(v_self_2959_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 2, v_rootNew_2938_);
v___x_3005_ = v___x_2977_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_self_2959_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_next_2960_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_rootNew_2938_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v_congr_2961_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v_target_x3f_2962_);
lean_ctor_set(v_reuseFailAlloc_3107_, 5, v_proof_x3f_2963_);
lean_ctor_set(v_reuseFailAlloc_3107_, 6, v_size_2965_);
lean_ctor_set(v_reuseFailAlloc_3107_, 7, v_idx_2970_);
lean_ctor_set(v_reuseFailAlloc_3107_, 8, v_generation_2971_);
lean_ctor_set(v_reuseFailAlloc_3107_, 9, v_mt_2972_);
lean_ctor_set(v_reuseFailAlloc_3107_, 10, v_sTerms_2973_);
lean_ctor_set(v_reuseFailAlloc_3107_, 11, v_ematchDiagSource_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12, v_flipped_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12 + 1, v_interpreted_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12 + 2, v_ctor_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12 + 3, v_hasLambdas_2968_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12 + 4, v_heqProofs_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_3107_, sizeof(void*)*12 + 5, v_funCC_2974_);
v___x_3005_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3004_;
}
v___jp_2979_:
{
size_t v___x_2980_; size_t v___x_2981_; uint8_t v___x_2982_; 
v___x_2980_ = lean_ptr_addr(v_next_2960_);
v___x_2981_ = lean_ptr_addr(v_lhs_2937_);
v___x_2982_ = lean_usize_dec_eq(v___x_2980_, v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2984_; 
lean_del_object(v___x_2957_);
lean_dec(v_snd_2948_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v_next_2960_);
lean_ctor_set(v___x_2950_, 0, v___x_2952_);
v___x_2984_ = v___x_2950_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_next_2960_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v_a_2940_ = v___x_2984_;
goto _start;
}
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec_ref(v_next_2960_);
lean_dec_ref(v_rootNew_2938_);
v___x_2987_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2987_);
v___x_2989_ = v___x_2950_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_snd_2948_);
v___x_2989_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2989_);
v___x_2991_ = v___x_2957_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
v___jp_2994_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_dec_ref_known(v___y_2995_, 1);
goto v___jp_2979_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_next_2960_);
lean_del_object(v___x_2957_);
lean_del_object(v___x_2950_);
lean_dec(v_snd_2948_);
lean_dec_ref(v_rootNew_2938_);
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___y_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___y_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___y_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; 
lean_inc_ref(v___x_3005_);
lean_inc_ref(v_self_2959_);
v___x_3006_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2959_, v___x_3005_, v___y_2941_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec_ref_known(v___x_3006_, 1);
if (v_a_2939_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
goto v___jp_2979_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3008_ = lean_unsigned_to_nat(3u);
v___x_3009_ = l_Lean_Expr_isAppOfArity(v_self_2959_, v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
goto v___jp_2979_;
}
else
{
uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3005_);
lean_dec_ref(v___x_3005_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v_toGoalState_3012_; lean_object* v_enodeMap_3013_; lean_object* v_congrTable_3014_; lean_object* v___x_3015_; 
v___x_3011_ = lean_st_ref_get(v___y_2941_);
v_toGoalState_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc_ref(v_toGoalState_3012_);
lean_dec(v___x_3011_);
v_enodeMap_3013_ = lean_ctor_get(v_toGoalState_3012_, 1);
lean_inc_ref(v_enodeMap_3013_);
v_congrTable_3014_ = lean_ctor_get(v_toGoalState_3012_, 4);
lean_inc_ref(v_congrTable_3014_);
lean_dec_ref(v_toGoalState_3012_);
lean_inc_ref(v_self_2959_);
v___x_3015_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3013_, v_congrTable_3014_, v_self_2959_);
lean_dec_ref(v_congrTable_3014_);
lean_dec_ref(v_enodeMap_3013_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
goto v___jp_2979_;
}
else
{
lean_object* v_val_3016_; lean_object* v_fst_3017_; lean_object* v___x_3018_; 
v_val_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v_fst_3017_ = lean_ctor_get(v_val_3016_, 0);
lean_inc(v_fst_3017_);
lean_dec(v_val_3016_);
v___x_3018_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3017_, v___y_2942_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; uint8_t v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = lean_unbox(v_a_3019_);
lean_dec(v_a_3019_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v_toGoalState_3022_; lean_object* v_mvarId_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3098_; 
v___x_3021_ = lean_st_ref_take(v___y_2941_);
v_toGoalState_3022_ = lean_ctor_get(v___x_3021_, 0);
v_mvarId_3023_ = lean_ctor_get(v___x_3021_, 1);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3025_ = v___x_3021_;
v_isShared_3026_ = v_isSharedCheck_3098_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_mvarId_3023_);
lean_inc(v_toGoalState_3022_);
lean_dec(v___x_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3098_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_nextDeclIdx_3027_; lean_object* v_enodeMap_3028_; lean_object* v_exprs_3029_; lean_object* v_parents_3030_; lean_object* v_congrTable_3031_; lean_object* v_appMap_3032_; lean_object* v_indicesFound_3033_; lean_object* v_toProcess_3034_; lean_object* v_internalizing_3035_; uint8_t v_inconsistent_3036_; lean_object* v_nextIdx_3037_; lean_object* v_newRawFacts_3038_; lean_object* v_facts_3039_; lean_object* v_extThms_3040_; lean_object* v_ematch_3041_; lean_object* v_inj_3042_; lean_object* v_split_3043_; lean_object* v_clean_3044_; lean_object* v_sstates_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3097_; 
v_nextDeclIdx_3027_ = lean_ctor_get(v_toGoalState_3022_, 0);
v_enodeMap_3028_ = lean_ctor_get(v_toGoalState_3022_, 1);
v_exprs_3029_ = lean_ctor_get(v_toGoalState_3022_, 2);
v_parents_3030_ = lean_ctor_get(v_toGoalState_3022_, 3);
v_congrTable_3031_ = lean_ctor_get(v_toGoalState_3022_, 4);
v_appMap_3032_ = lean_ctor_get(v_toGoalState_3022_, 5);
v_indicesFound_3033_ = lean_ctor_get(v_toGoalState_3022_, 6);
v_toProcess_3034_ = lean_ctor_get(v_toGoalState_3022_, 7);
v_internalizing_3035_ = lean_ctor_get(v_toGoalState_3022_, 8);
v_inconsistent_3036_ = lean_ctor_get_uint8(v_toGoalState_3022_, sizeof(void*)*18);
v_nextIdx_3037_ = lean_ctor_get(v_toGoalState_3022_, 9);
v_newRawFacts_3038_ = lean_ctor_get(v_toGoalState_3022_, 10);
v_facts_3039_ = lean_ctor_get(v_toGoalState_3022_, 11);
v_extThms_3040_ = lean_ctor_get(v_toGoalState_3022_, 12);
v_ematch_3041_ = lean_ctor_get(v_toGoalState_3022_, 13);
v_inj_3042_ = lean_ctor_get(v_toGoalState_3022_, 14);
v_split_3043_ = lean_ctor_get(v_toGoalState_3022_, 15);
v_clean_3044_ = lean_ctor_get(v_toGoalState_3022_, 16);
v_sstates_3045_ = lean_ctor_get(v_toGoalState_3022_, 17);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_toGoalState_3022_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3047_ = v_toGoalState_3022_;
v_isShared_3048_ = v_isSharedCheck_3097_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_sstates_3045_);
lean_inc(v_clean_3044_);
lean_inc(v_split_3043_);
lean_inc(v_inj_3042_);
lean_inc(v_ematch_3041_);
lean_inc(v_extThms_3040_);
lean_inc(v_facts_3039_);
lean_inc(v_newRawFacts_3038_);
lean_inc(v_nextIdx_3037_);
lean_inc(v_internalizing_3035_);
lean_inc(v_toProcess_3034_);
lean_inc(v_indicesFound_3033_);
lean_inc(v_appMap_3032_);
lean_inc(v_congrTable_3031_);
lean_inc(v_parents_3030_);
lean_inc(v_exprs_3029_);
lean_inc(v_enodeMap_3028_);
lean_inc(v_nextDeclIdx_3027_);
lean_dec(v_toGoalState_3022_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3097_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = lean_box(0);
lean_inc_ref(v_self_2959_);
v___x_3050_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3028_, v_congrTable_3031_, v_self_2959_, v___x_3049_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 4, v___x_3050_);
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_nextDeclIdx_3027_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_enodeMap_3028_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_exprs_3029_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_parents_3030_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3096_, 5, v_appMap_3032_);
lean_ctor_set(v_reuseFailAlloc_3096_, 6, v_indicesFound_3033_);
lean_ctor_set(v_reuseFailAlloc_3096_, 7, v_toProcess_3034_);
lean_ctor_set(v_reuseFailAlloc_3096_, 8, v_internalizing_3035_);
lean_ctor_set(v_reuseFailAlloc_3096_, 9, v_nextIdx_3037_);
lean_ctor_set(v_reuseFailAlloc_3096_, 10, v_newRawFacts_3038_);
lean_ctor_set(v_reuseFailAlloc_3096_, 11, v_facts_3039_);
lean_ctor_set(v_reuseFailAlloc_3096_, 12, v_extThms_3040_);
lean_ctor_set(v_reuseFailAlloc_3096_, 13, v_ematch_3041_);
lean_ctor_set(v_reuseFailAlloc_3096_, 14, v_inj_3042_);
lean_ctor_set(v_reuseFailAlloc_3096_, 15, v_split_3043_);
lean_ctor_set(v_reuseFailAlloc_3096_, 16, v_clean_3044_);
lean_ctor_set(v_reuseFailAlloc_3096_, 17, v_sstates_3045_);
lean_ctor_set_uint8(v_reuseFailAlloc_3096_, sizeof(void*)*18, v_inconsistent_3036_);
v___x_3052_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3052_);
v___x_3054_ = v___x_3025_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_mvarId_3023_);
v___x_3054_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_st_ref_put(v___y_2941_, v___x_3054_);
lean_inc_ref(v_rootNew_2938_);
lean_inc_ref(v_next_2960_);
lean_inc_ref_n(v_self_2959_, 3);
v___x_3056_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3056_, 0, v_self_2959_);
lean_ctor_set(v___x_3056_, 1, v_next_2960_);
lean_ctor_set(v___x_3056_, 2, v_rootNew_2938_);
lean_ctor_set(v___x_3056_, 3, v_self_2959_);
lean_ctor_set(v___x_3056_, 4, v_target_x3f_2962_);
lean_ctor_set(v___x_3056_, 5, v_proof_x3f_2963_);
lean_ctor_set(v___x_3056_, 6, v_size_2965_);
lean_ctor_set(v___x_3056_, 7, v_idx_2970_);
lean_ctor_set(v___x_3056_, 8, v_generation_2971_);
lean_ctor_set(v___x_3056_, 9, v_mt_2972_);
lean_ctor_set(v___x_3056_, 10, v_sTerms_2973_);
lean_ctor_set(v___x_3056_, 11, v_ematchDiagSource_2975_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12, v_flipped_2964_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12 + 1, v_interpreted_2966_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12 + 2, v_ctor_2967_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12 + 3, v_hasLambdas_2968_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12 + 4, v_heqProofs_2969_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*12 + 5, v_funCC_2974_);
v___x_3057_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2959_, v___x_3056_, v___y_2941_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_dec_ref_known(v___x_3057_, 1);
v___x_3058_ = lean_st_ref_get(v___y_2941_);
lean_inc(v_fst_3017_);
v___x_3059_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3058_, v_fst_3017_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___x_3058_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v_self_3061_; lean_object* v_next_3062_; lean_object* v_root_3063_; lean_object* v_target_x3f_3064_; lean_object* v_proof_x3f_3065_; uint8_t v_flipped_3066_; lean_object* v_size_3067_; uint8_t v_interpreted_3068_; uint8_t v_ctor_3069_; uint8_t v_hasLambdas_3070_; uint8_t v_heqProofs_3071_; lean_object* v_idx_3072_; lean_object* v_generation_3073_; lean_object* v_mt_3074_; lean_object* v_sTerms_3075_; uint8_t v_funCC_3076_; lean_object* v_ematchDiagSource_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3085_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v_self_3061_ = lean_ctor_get(v_a_3060_, 0);
v_next_3062_ = lean_ctor_get(v_a_3060_, 1);
v_root_3063_ = lean_ctor_get(v_a_3060_, 2);
v_target_x3f_3064_ = lean_ctor_get(v_a_3060_, 4);
v_proof_x3f_3065_ = lean_ctor_get(v_a_3060_, 5);
v_flipped_3066_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12);
v_size_3067_ = lean_ctor_get(v_a_3060_, 6);
v_interpreted_3068_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12 + 1);
v_ctor_3069_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12 + 2);
v_hasLambdas_3070_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12 + 3);
v_heqProofs_3071_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12 + 4);
v_idx_3072_ = lean_ctor_get(v_a_3060_, 7);
v_generation_3073_ = lean_ctor_get(v_a_3060_, 8);
v_mt_3074_ = lean_ctor_get(v_a_3060_, 9);
v_sTerms_3075_ = lean_ctor_get(v_a_3060_, 10);
v_funCC_3076_ = lean_ctor_get_uint8(v_a_3060_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3077_ = lean_ctor_get(v_a_3060_, 11);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v_a_3060_, 3);
lean_dec(v_unused_3086_);
v___x_3079_ = v_a_3060_;
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_ematchDiagSource_3077_);
lean_inc(v_sTerms_3075_);
lean_inc(v_mt_3074_);
lean_inc(v_generation_3073_);
lean_inc(v_idx_3072_);
lean_inc(v_size_3067_);
lean_inc(v_proof_x3f_3065_);
lean_inc(v_target_x3f_3064_);
lean_inc(v_root_3063_);
lean_inc(v_next_3062_);
lean_inc(v_self_3061_);
lean_dec(v_a_3060_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 3, v_self_2959_);
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_self_3061_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_next_3062_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_root_3063_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_self_2959_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_target_x3f_3064_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_proof_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_size_3067_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_idx_3072_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_generation_3073_);
lean_ctor_set(v_reuseFailAlloc_3084_, 9, v_mt_3074_);
lean_ctor_set(v_reuseFailAlloc_3084_, 10, v_sTerms_3075_);
lean_ctor_set(v_reuseFailAlloc_3084_, 11, v_ematchDiagSource_3077_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12, v_flipped_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 1, v_interpreted_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 2, v_ctor_3069_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 3, v_hasLambdas_3070_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 4, v_heqProofs_3071_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 5, v_funCC_3076_);
v___x_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3017_, v___x_3082_, v___y_2941_);
v___y_2995_ = v___x_3083_;
goto v___jp_2994_;
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_fst_3017_);
lean_dec_ref(v_next_2960_);
lean_dec_ref(v_self_2959_);
lean_del_object(v___x_2957_);
lean_del_object(v___x_2950_);
lean_dec(v_snd_2948_);
lean_dec_ref(v_rootNew_2938_);
v_a_3087_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3059_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3059_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_dec(v_fst_3017_);
lean_dec_ref(v_self_2959_);
v___y_2995_ = v___x_3057_;
goto v___jp_2994_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3017_);
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
goto v___jp_2979_;
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_fst_3017_);
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_next_2960_);
lean_dec_ref(v_self_2959_);
lean_del_object(v___x_2957_);
lean_del_object(v___x_2950_);
lean_dec(v_snd_2948_);
lean_dec_ref(v_rootNew_2938_);
v_a_3099_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3018_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3018_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
goto v___jp_2979_;
}
}
}
}
else
{
lean_dec_ref(v___x_3005_);
lean_dec(v_ematchDiagSource_2975_);
lean_dec(v_sTerms_2973_);
lean_dec(v_mt_2972_);
lean_dec(v_generation_2971_);
lean_dec(v_idx_2970_);
lean_dec(v_size_2965_);
lean_dec(v_proof_x3f_2963_);
lean_dec(v_target_x3f_2962_);
lean_dec_ref(v_self_2959_);
v___y_2995_ = v___x_3006_;
goto v___jp_2994_;
}
}
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_del_object(v___x_2950_);
lean_dec(v_snd_2948_);
lean_dec_ref(v_rootNew_2938_);
v_a_3111_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_2954_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_2954_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3121_, lean_object* v_rootNew_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
uint8_t v_a_26413__boxed_3132_; lean_object* v_res_3133_; 
v_a_26413__boxed_3132_ = lean_unbox(v_a_3123_);
v_res_3133_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3121_, v_rootNew_3122_, v_a_26413__boxed_3132_, v_a_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v_lhs_3121_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3134_, lean_object* v_rootNew_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3135_, v_a_3140_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = lean_box(0);
lean_inc_ref(v_lhs_3134_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v_lhs_3134_);
v___x_3151_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
v___x_3152_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3134_, v_rootNew_3135_, v___x_3151_, v___x_3150_, v_a_3136_, v_a_3140_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
lean_dec_ref(v_lhs_3134_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3166_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; 
v_fst_3157_ = lean_ctor_get(v_a_3153_, 0);
lean_inc(v_fst_3157_);
lean_dec(v_a_3153_);
if (lean_obj_tag(v_fst_3157_) == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3158_ = lean_box(0);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3158_);
v___x_3160_ = v___x_3155_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
else
{
lean_object* v_val_3162_; lean_object* v___x_3164_; 
v_val_3162_ = lean_ctor_get(v_fst_3157_, 0);
lean_inc(v_val_3162_);
lean_dec_ref_known(v_fst_3157_, 1);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v_val_3162_);
v___x_3164_ = v___x_3155_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_val_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_a_3167_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3152_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3152_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_rootNew_3135_);
lean_dec_ref(v_lhs_3134_);
v_a_3175_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3147_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3147_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3183_, lean_object* v_rootNew_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3183_, v_rootNew_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec(v_a_3185_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3197_, lean_object* v_00_u03b2_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3197_, v_x_3199_, v_x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3202_, v_00_u03b2_3203_, v_x_3204_, v_x_3205_);
lean_dec_ref(v_x_3204_);
lean_dec_ref(v___x_3202_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3207_, lean_object* v_00_u03b2_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3207_, v_x_3209_, v_x_3210_, v_x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3213_, v_00_u03b2_3214_, v_x_3215_, v_x_3216_, v_x_3217_);
lean_dec_ref(v___x_3213_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3219_, lean_object* v_rootNew_3220_, uint8_t v_a_3221_, lean_object* v_inst_3222_, lean_object* v_a_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3219_, v_rootNew_3220_, v_a_3221_, v_a_3223_, v___y_3224_, v___y_3228_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3236_, lean_object* v_rootNew_3237_, lean_object* v_a_3238_, lean_object* v_inst_3239_, lean_object* v_a_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
uint8_t v_a_26772__boxed_3252_; lean_object* v_res_3253_; 
v_a_26772__boxed_3252_ = lean_unbox(v_a_3238_);
v_res_3253_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3236_, v_rootNew_3237_, v_a_26772__boxed_3252_, v_inst_3239_, v_a_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v_lhs_3236_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3254_, lean_object* v_00_u03b2_3255_, lean_object* v_x_3256_, size_t v_x_3257_, lean_object* v_x_3258_){
_start:
{
lean_object* v___x_3259_; 
lean_inc_ref(v_x_3256_);
v___x_3259_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3254_, v_x_3256_, v_x_3257_, v_x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3260_, lean_object* v_00_u03b2_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
size_t v_x_26815__boxed_3265_; lean_object* v_res_3266_; 
v_x_26815__boxed_3265_ = lean_unbox_usize(v_x_3263_);
lean_dec(v_x_3263_);
v_res_3266_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3260_, v_00_u03b2_3261_, v_x_3262_, v_x_26815__boxed_3265_, v_x_3264_);
lean_dec_ref(v_x_3262_);
lean_dec_ref(v___x_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3267_, lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, size_t v_x_3270_, size_t v_x_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3267_, v_x_3269_, v_x_3270_, v_x_3271_, v_x_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
size_t v_x_26829__boxed_3282_; size_t v_x_26830__boxed_3283_; lean_object* v_res_3284_; 
v_x_26829__boxed_3282_ = lean_unbox_usize(v_x_3278_);
lean_dec(v_x_3278_);
v_x_26830__boxed_3283_ = lean_unbox_usize(v_x_3279_);
lean_dec(v_x_3279_);
v_res_3284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3275_, v_00_u03b2_3276_, v_x_3277_, v_x_26829__boxed_3282_, v_x_26830__boxed_3283_, v_x_3280_, v_x_3281_);
lean_dec_ref(v___x_3275_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3285_, lean_object* v_00_u03b2_3286_, lean_object* v_keys_3287_, lean_object* v_vals_3288_, lean_object* v_heq_3289_, lean_object* v_i_3290_, lean_object* v_k_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3285_, v_keys_3287_, v_vals_3288_, v_i_3290_, v_k_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3293_, lean_object* v_00_u03b2_3294_, lean_object* v_keys_3295_, lean_object* v_vals_3296_, lean_object* v_heq_3297_, lean_object* v_i_3298_, lean_object* v_k_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3293_, v_00_u03b2_3294_, v_keys_3295_, v_vals_3296_, v_heq_3297_, v_i_3298_, v_k_3299_);
lean_dec_ref(v_vals_3296_);
lean_dec_ref(v_keys_3295_);
lean_dec_ref(v___x_3293_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3301_, lean_object* v_00_u03b2_3302_, lean_object* v_n_3303_, lean_object* v_k_3304_, lean_object* v_v_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3301_, v_n_3303_, v_k_3304_, v_v_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3307_, lean_object* v_00_u03b2_3308_, lean_object* v_n_3309_, lean_object* v_k_3310_, lean_object* v_v_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3307_, v_00_u03b2_3308_, v_n_3309_, v_k_3310_, v_v_3311_);
lean_dec_ref(v___x_3307_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3313_, lean_object* v_00_u03b2_3314_, size_t v_depth_3315_, lean_object* v_keys_3316_, lean_object* v_vals_3317_, lean_object* v_heq_3318_, lean_object* v_i_3319_, lean_object* v_entries_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3313_, v_depth_3315_, v_keys_3316_, v_vals_3317_, v_i_3319_, v_entries_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3322_, lean_object* v_00_u03b2_3323_, lean_object* v_depth_3324_, lean_object* v_keys_3325_, lean_object* v_vals_3326_, lean_object* v_heq_3327_, lean_object* v_i_3328_, lean_object* v_entries_3329_){
_start:
{
size_t v_depth_boxed_3330_; lean_object* v_res_3331_; 
v_depth_boxed_3330_ = lean_unbox_usize(v_depth_3324_);
lean_dec(v_depth_3324_);
v_res_3331_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3322_, v_00_u03b2_3323_, v_depth_boxed_3330_, v_keys_3325_, v_vals_3326_, v_heq_3327_, v_i_3328_, v_entries_3329_);
lean_dec_ref(v_vals_3326_);
lean_dec_ref(v_keys_3325_);
lean_dec_ref(v___x_3322_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3332_, lean_object* v_00_u03b2_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3332_, v_x_3334_, v_x_3335_, v_x_3336_, v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3339_, v_00_u03b2_3340_, v_x_3341_, v_x_3342_, v_x_3343_, v_x_3344_);
lean_dec_ref(v___x_3339_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3346_, lean_object* v_b_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
if (lean_obj_tag(v_as_x27_3346_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v_b_3347_);
return v___x_3359_;
}
else
{
lean_object* v_head_3360_; lean_object* v_tail_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_head_3360_ = lean_ctor_get(v_as_x27_3346_, 0);
v_tail_3361_ = lean_ctor_get(v_as_x27_3346_, 1);
v___x_3362_ = lean_box(0);
lean_inc(v_head_3360_);
v___x_3363_ = l_Lean_Meta_Grind_propagateUp(v_head_3360_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_dec_ref_known(v___x_3363_, 1);
v_as_x27_3346_ = v_tail_3361_;
v_b_3347_ = v___x_3362_;
goto _start;
}
else
{
return v___x_3363_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3365_, lean_object* v_b_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3365_, v_b_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v_as_x27_3365_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3379_, lean_object* v_b_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
if (lean_obj_tag(v_as_x27_3379_) == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_b_3380_);
return v___x_3392_;
}
else
{
lean_object* v_head_3393_; lean_object* v_tail_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_head_3393_ = lean_ctor_get(v_as_x27_3379_, 0);
v_tail_3394_ = lean_ctor_get(v_as_x27_3379_, 1);
v___x_3395_ = lean_box(0);
lean_inc(v_head_3393_);
v___x_3396_ = l_Lean_Meta_Grind_propagateDown(v_head_3393_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_dec_ref_known(v___x_3396_, 1);
v_as_x27_3379_ = v_tail_3394_;
v_b_3380_ = v___x_3395_;
goto _start;
}
else
{
return v___x_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3398_, lean_object* v_b_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3398_, v_b_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v_as_x27_3398_);
return v_res_3411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_cls_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3416_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3417_ = l_Lean_Name_append(v___x_3416_, v_cls_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3430_, uint8_t v_isHEq_3431_, lean_object* v_lhs_3432_, lean_object* v_rhs_3433_, lean_object* v_lhsNode_3434_, lean_object* v_rhsNode_3435_, lean_object* v_lhsRoot_3436_, lean_object* v_rhsRoot_3437_, uint8_t v_flipped_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3568_; uint8_t v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; uint8_t v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; uint8_t v___y_3604_; uint8_t v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v_toCold_3688_; lean_object* v_options_3689_; lean_object* v_inheritedTraceOptions_3690_; uint8_t v_hasTrace_3691_; lean_object* v_cls_3692_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v_fns_u2082_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v_fns_u2081_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; 
v_toCold_3688_ = lean_ctor_get(v_a_3447_, 0);
v_options_3689_ = lean_ctor_get(v_toCold_3688_, 2);
v_inheritedTraceOptions_3690_ = lean_ctor_get(v_toCold_3688_, 11);
v_hasTrace_3691_ = lean_ctor_get_uint8(v_options_3689_, sizeof(void*)*1);
v_cls_3692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3691_ == 0)
{
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3690_, v_options_3689_, v___x_3892_);
if (v___x_3893_ == 0)
{
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_Meta_Grind_updateLastTag(v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v___x_3895_; 
lean_dec_ref_known(v___x_3894_, 1);
lean_inc_ref(v_lhs_3432_);
v___x_3895_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3432_, v_a_3439_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
lean_inc_ref(v_rhs_3433_);
v___x_3897_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3433_, v_a_3439_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v_a_3896_);
v___x_3901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v_a_3898_);
v___x_3904_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3692_, v___x_3903_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_dec_ref_known(v___x_3904_, 1);
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
v___y_3819_ = v_a_3446_;
v___y_3820_ = v_a_3447_;
v___y_3821_ = v_a_3448_;
goto v___jp_3811_;
}
else
{
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhsNode_3434_);
lean_dec_ref(v_rhs_3433_);
lean_dec_ref(v_lhs_3432_);
lean_dec_ref(v_proof_3430_);
return v___x_3904_;
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_a_3896_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhsNode_3434_);
lean_dec_ref(v_rhs_3433_);
lean_dec_ref(v_lhs_3432_);
lean_dec_ref(v_proof_3430_);
v_a_3905_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3897_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3897_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhsNode_3434_);
lean_dec_ref(v_rhs_3433_);
lean_dec_ref(v_lhs_3432_);
lean_dec_ref(v_proof_3430_);
v_a_3913_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3895_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3895_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhsNode_3434_);
lean_dec_ref(v_rhs_3433_);
lean_dec_ref(v_lhs_3432_);
lean_dec_ref(v_proof_3430_);
return v___x_3894_;
}
}
}
v___jp_3450_:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3457_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3493_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3470_ = v___x_3467_;
v_isShared_3471_ = v_isSharedCheck_3493_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3493_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_unbox(v_a_3468_);
lean_dec(v_a_3468_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_del_object(v___x_3470_);
v___x_3473_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3456_);
lean_dec(v___y_3456_);
v___x_3474_ = lean_box(0);
v___x_3475_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3473_, v___x_3474_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___x_3473_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref_known(v___x_3475_, 1);
v___x_3476_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3454_, v___x_3474_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref_known(v___x_3476_, 1);
v___x_3477_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3453_, v___y_3451_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v___y_3453_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref_known(v___x_3477_, 1);
v___x_3478_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3452_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3487_; 
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3478_, 0);
lean_dec(v_unused_3488_);
v___x_3480_ = v___x_3478_;
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
else
{
lean_dec(v___x_3478_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
uint8_t v___x_3482_; 
v___x_3482_ = l_Lean_Expr_isTrue(v___y_3455_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3484_; 
lean_dec(v___y_3454_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3474_);
v___x_3484_ = v___x_3480_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3474_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
else
{
lean_object* v___x_3486_; 
lean_del_object(v___x_3480_);
v___x_3486_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3454_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3454_);
return v___x_3486_;
}
}
}
else
{
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
return v___x_3478_;
}
}
else
{
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3452_);
return v___x_3477_;
}
}
else
{
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
return v___x_3476_;
}
}
else
{
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
return v___x_3475_;
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
v___x_3489_ = lean_box(0);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3489_);
v___x_3491_ = v___x_3470_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
v_a_3494_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3467_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3467_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
v___jp_3502_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_inc_ref(v___y_3509_);
v___x_3539_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3539_, 0, v___y_3509_);
lean_ctor_set(v___x_3539_, 1, v___y_3523_);
lean_ctor_set(v___x_3539_, 2, v___y_3503_);
lean_ctor_set(v___x_3539_, 3, v___y_3519_);
lean_ctor_set(v___x_3539_, 4, v___y_3530_);
lean_ctor_set(v___x_3539_, 5, v___y_3524_);
lean_ctor_set(v___x_3539_, 6, v___y_3516_);
lean_ctor_set(v___x_3539_, 7, v___y_3535_);
lean_ctor_set(v___x_3539_, 8, v___y_3504_);
lean_ctor_set(v___x_3539_, 9, v___y_3506_);
lean_ctor_set(v___x_3539_, 10, v___y_3507_);
lean_ctor_set(v___x_3539_, 11, v___y_3508_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12, v___y_3515_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12 + 1, v___y_3534_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12 + 2, v___y_3505_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12 + 3, v___y_3529_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12 + 4, v___y_3538_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*12 + 5, v___y_3531_);
lean_inc_ref(v___y_3532_);
v___x_3540_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3532_, v___x_3539_, v___y_3536_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3541_; 
lean_dec_ref_known(v___x_3540_, 1);
lean_inc_ref(v___y_3520_);
v___x_3541_ = l_Lean_Meta_Grind_propagateBeta(v___y_3520_, v___y_3518_, v___y_3536_, v___y_3514_, v___y_3525_, v___y_3537_, v___y_3512_, v___y_3511_, v___y_3510_, v___y_3528_, v___y_3533_, v___y_3517_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v___x_3542_; 
lean_dec_ref_known(v___x_3541_, 1);
lean_inc_ref(v___y_3526_);
v___x_3542_ = l_Lean_Meta_Grind_propagateBeta(v___y_3526_, v___y_3522_, v___y_3536_, v___y_3514_, v___y_3525_, v___y_3537_, v___y_3512_, v___y_3511_, v___y_3510_, v___y_3528_, v___y_3533_, v___y_3517_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref_known(v___x_3542_, 1);
v___x_3543_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3437_, v_lhsRoot_3436_, v___y_3536_, v___y_3510_, v___y_3528_, v___y_3533_, v___y_3517_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3521_, v___y_3536_);
lean_dec_ref(v___y_3521_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3545_, 1);
lean_inc_ref(v___y_3532_);
v___x_3546_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3513_, v___y_3532_, v___y_3536_, v___y_3514_, v___y_3525_, v___y_3537_, v___y_3512_, v___y_3511_, v___y_3510_, v___y_3528_, v___y_3533_, v___y_3517_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3546_, 1);
v___x_3547_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3536_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; uint8_t v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___x_3549_ = lean_unbox(v_a_3548_);
lean_dec(v_a_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3509_, v___y_3536_, v___y_3514_, v___y_3525_, v___y_3537_, v___y_3512_, v___y_3511_, v___y_3510_, v___y_3528_, v___y_3533_, v___y_3517_);
lean_dec_ref(v___y_3509_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_dec_ref_known(v___x_3550_, 1);
v___y_3451_ = v___y_3526_;
v___y_3452_ = v_a_3544_;
v___y_3453_ = v___y_3520_;
v___y_3454_ = v___y_3527_;
v___y_3455_ = v___y_3532_;
v___y_3456_ = v___y_3513_;
v___y_3457_ = v___y_3536_;
v___y_3458_ = v___y_3514_;
v___y_3459_ = v___y_3525_;
v___y_3460_ = v___y_3537_;
v___y_3461_ = v___y_3512_;
v___y_3462_ = v___y_3511_;
v___y_3463_ = v___y_3510_;
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3533_;
v___y_3466_ = v___y_3517_;
goto v___jp_3450_;
}
else
{
lean_dec(v_a_3544_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
return v___x_3550_;
}
}
else
{
lean_dec_ref(v___y_3509_);
v___y_3451_ = v___y_3526_;
v___y_3452_ = v_a_3544_;
v___y_3453_ = v___y_3520_;
v___y_3454_ = v___y_3527_;
v___y_3455_ = v___y_3532_;
v___y_3456_ = v___y_3513_;
v___y_3457_ = v___y_3536_;
v___y_3458_ = v___y_3514_;
v___y_3459_ = v___y_3525_;
v___y_3460_ = v___y_3537_;
v___y_3461_ = v___y_3512_;
v___y_3462_ = v___y_3511_;
v___y_3463_ = v___y_3510_;
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3533_;
v___y_3466_ = v___y_3517_;
goto v___jp_3450_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_a_3544_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
v_a_3551_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3547_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3547_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_dec(v_a_3544_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
return v___x_3546_;
}
}
else
{
lean_dec(v_a_3544_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
return v___x_3545_;
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
v_a_3559_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3543_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3543_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
return v___x_3542_;
}
}
else
{
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
return v___x_3541_;
}
}
else
{
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
return v___x_3540_;
}
}
v___jp_3567_:
{
if (v_isHEq_3431_ == 0)
{
if (v___y_3603_ == 0)
{
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3569_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3571_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3593_;
v___y_3529_ = v___y_3604_;
v___y_3530_ = v___y_3595_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3596_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3598_;
v___y_3535_ = v___y_3600_;
v___y_3536_ = v___y_3601_;
v___y_3537_ = v___y_3602_;
v___y_3538_ = v___y_3578_;
goto v___jp_3502_;
}
else
{
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3569_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3571_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3593_;
v___y_3529_ = v___y_3604_;
v___y_3530_ = v___y_3595_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3596_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3598_;
v___y_3535_ = v___y_3600_;
v___y_3536_ = v___y_3601_;
v___y_3537_ = v___y_3602_;
v___y_3538_ = v___y_3603_;
goto v___jp_3502_;
}
}
else
{
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3569_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3571_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3594_;
v___y_3528_ = v___y_3593_;
v___y_3529_ = v___y_3604_;
v___y_3530_ = v___y_3595_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3596_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3598_;
v___y_3535_ = v___y_3600_;
v___y_3536_ = v___y_3601_;
v___y_3537_ = v___y_3602_;
v___y_3538_ = v_isHEq_3431_;
goto v___jp_3502_;
}
}
v___jp_3605_:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3616_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3628_) == 0)
{
uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_dec_ref_known(v___x_3628_, 1);
v___x_3629_ = 0;
v___x_3630_ = lean_st_ref_get(v___y_3618_);
v___x_3631_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3630_, v_lhs_3432_, v___x_3629_);
lean_dec(v___x_3630_);
v___x_3632_ = lean_st_ref_get(v___y_3618_);
lean_inc_ref(v___y_3612_);
v___x_3633_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3632_, v___y_3612_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___x_3632_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_self_3635_; lean_object* v_root_3636_; lean_object* v_congr_3637_; lean_object* v_target_x3f_3638_; lean_object* v_proof_x3f_3639_; uint8_t v_flipped_3640_; lean_object* v_size_3641_; uint8_t v_interpreted_3642_; uint8_t v_ctor_3643_; uint8_t v_hasLambdas_3644_; uint8_t v_heqProofs_3645_; lean_object* v_idx_3646_; lean_object* v_generation_3647_; lean_object* v_mt_3648_; lean_object* v_sTerms_3649_; uint8_t v_funCC_3650_; lean_object* v_ematchDiagSource_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3678_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v_self_3635_ = lean_ctor_get(v_a_3634_, 0);
v_root_3636_ = lean_ctor_get(v_a_3634_, 2);
v_congr_3637_ = lean_ctor_get(v_a_3634_, 3);
v_target_x3f_3638_ = lean_ctor_get(v_a_3634_, 4);
v_proof_x3f_3639_ = lean_ctor_get(v_a_3634_, 5);
v_flipped_3640_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12);
v_size_3641_ = lean_ctor_get(v_a_3634_, 6);
v_interpreted_3642_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12 + 1);
v_ctor_3643_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12 + 2);
v_hasLambdas_3644_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12 + 3);
v_heqProofs_3645_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12 + 4);
v_idx_3646_ = lean_ctor_get(v_a_3634_, 7);
v_generation_3647_ = lean_ctor_get(v_a_3634_, 8);
v_mt_3648_ = lean_ctor_get(v_a_3634_, 9);
v_sTerms_3649_ = lean_ctor_get(v_a_3634_, 10);
v_funCC_3650_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3651_ = lean_ctor_get(v_a_3634_, 11);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_a_3634_, 1);
lean_dec(v_unused_3679_);
v___x_3653_ = v_a_3634_;
v_isShared_3654_ = v_isSharedCheck_3678_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_ematchDiagSource_3651_);
lean_inc(v_sTerms_3649_);
lean_inc(v_mt_3648_);
lean_inc(v_generation_3647_);
lean_inc(v_idx_3646_);
lean_inc(v_size_3641_);
lean_inc(v_proof_x3f_3639_);
lean_inc(v_target_x3f_3638_);
lean_inc(v_congr_3637_);
lean_inc(v_root_3636_);
lean_inc(v_self_3635_);
lean_dec(v_a_3634_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3678_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_self_3655_; lean_object* v_next_3656_; lean_object* v_root_3657_; lean_object* v_congr_3658_; lean_object* v_target_x3f_3659_; lean_object* v_proof_x3f_3660_; uint8_t v_flipped_3661_; lean_object* v_size_3662_; uint8_t v_interpreted_3663_; uint8_t v_ctor_3664_; uint8_t v_hasLambdas_3665_; uint8_t v_heqProofs_3666_; lean_object* v_idx_3667_; lean_object* v_generation_3668_; lean_object* v_mt_3669_; lean_object* v_sTerms_3670_; uint8_t v_funCC_3671_; lean_object* v_ematchDiagSource_3672_; lean_object* v___x_3674_; 
v_self_3655_ = lean_ctor_get(v_rhsRoot_3437_, 0);
v_next_3656_ = lean_ctor_get(v_rhsRoot_3437_, 1);
v_root_3657_ = lean_ctor_get(v_rhsRoot_3437_, 2);
v_congr_3658_ = lean_ctor_get(v_rhsRoot_3437_, 3);
v_target_x3f_3659_ = lean_ctor_get(v_rhsRoot_3437_, 4);
v_proof_x3f_3660_ = lean_ctor_get(v_rhsRoot_3437_, 5);
v_flipped_3661_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12);
v_size_3662_ = lean_ctor_get(v_rhsRoot_3437_, 6);
v_interpreted_3663_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12 + 1);
v_ctor_3664_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12 + 2);
v_hasLambdas_3665_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12 + 3);
v_heqProofs_3666_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12 + 4);
v_idx_3667_ = lean_ctor_get(v_rhsRoot_3437_, 7);
v_generation_3668_ = lean_ctor_get(v_rhsRoot_3437_, 8);
v_mt_3669_ = lean_ctor_get(v_rhsRoot_3437_, 9);
v_sTerms_3670_ = lean_ctor_get(v_rhsRoot_3437_, 10);
v_funCC_3671_ = lean_ctor_get_uint8(v_rhsRoot_3437_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3672_ = lean_ctor_get(v_rhsRoot_3437_, 11);
lean_inc_ref(v_next_3656_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v_next_3656_);
v___x_3674_ = v___x_3653_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_self_3635_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_next_3656_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_root_3636_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v_congr_3637_);
lean_ctor_set(v_reuseFailAlloc_3677_, 4, v_target_x3f_3638_);
lean_ctor_set(v_reuseFailAlloc_3677_, 5, v_proof_x3f_3639_);
lean_ctor_set(v_reuseFailAlloc_3677_, 6, v_size_3641_);
lean_ctor_set(v_reuseFailAlloc_3677_, 7, v_idx_3646_);
lean_ctor_set(v_reuseFailAlloc_3677_, 8, v_generation_3647_);
lean_ctor_set(v_reuseFailAlloc_3677_, 9, v_mt_3648_);
lean_ctor_set(v_reuseFailAlloc_3677_, 10, v_sTerms_3649_);
lean_ctor_set(v_reuseFailAlloc_3677_, 11, v_ematchDiagSource_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12, v_flipped_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12 + 1, v_interpreted_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12 + 2, v_ctor_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12 + 3, v_hasLambdas_3644_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12 + 4, v_heqProofs_3645_);
lean_ctor_set_uint8(v_reuseFailAlloc_3677_, sizeof(void*)*12 + 5, v_funCC_3650_);
v___x_3674_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3615_, v___x_3674_, v___y_3618_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v___x_3676_; 
lean_dec_ref_known(v___x_3675_, 1);
v___x_3676_ = lean_nat_add(v_size_3662_, v___y_3610_);
lean_dec(v___y_3610_);
if (v_hasLambdas_3665_ == 0)
{
lean_inc(v_idx_3667_);
lean_inc(v_target_x3f_3659_);
lean_inc(v_proof_x3f_3660_);
lean_inc_ref(v_congr_3658_);
lean_inc_ref(v_self_3655_);
lean_inc(v_mt_3669_);
lean_inc(v_sTerms_3670_);
lean_inc(v_ematchDiagSource_3672_);
lean_inc(v_generation_3668_);
lean_inc_ref(v_root_3657_);
v___y_3568_ = v_root_3657_;
v___y_3569_ = v_ctor_3664_;
v___y_3570_ = v_generation_3668_;
v___y_3571_ = v_ematchDiagSource_3672_;
v___y_3572_ = v_sTerms_3670_;
v___y_3573_ = v_mt_3669_;
v___y_3574_ = v_self_3655_;
v___y_3575_ = v___y_3624_;
v___y_3576_ = v___y_3623_;
v___y_3577_ = v___y_3622_;
v___y_3578_ = v___y_3614_;
v___y_3579_ = v___y_3616_;
v___y_3580_ = v___y_3619_;
v___y_3581_ = v_flipped_3661_;
v___y_3582_ = v___x_3676_;
v___y_3583_ = v___y_3627_;
v___y_3584_ = v___y_3608_;
v___y_3585_ = v_congr_3658_;
v___y_3586_ = v___y_3609_;
v___y_3587_ = v___y_3612_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v___y_3617_;
v___y_3590_ = v_proof_x3f_3660_;
v___y_3591_ = v___y_3620_;
v___y_3592_ = v___y_3607_;
v___y_3593_ = v___y_3625_;
v___y_3594_ = v___x_3631_;
v___y_3595_ = v_target_x3f_3659_;
v___y_3596_ = v___y_3613_;
v___y_3597_ = v_funCC_3671_;
v___y_3598_ = v_interpreted_3663_;
v___y_3599_ = v___y_3626_;
v___y_3600_ = v_idx_3667_;
v___y_3601_ = v___y_3618_;
v___y_3602_ = v___y_3621_;
v___y_3603_ = v_heqProofs_3666_;
v___y_3604_ = v___y_3606_;
goto v___jp_3567_;
}
else
{
lean_inc(v_idx_3667_);
lean_inc(v_target_x3f_3659_);
lean_inc(v_proof_x3f_3660_);
lean_inc_ref(v_congr_3658_);
lean_inc_ref(v_self_3655_);
lean_inc(v_mt_3669_);
lean_inc(v_sTerms_3670_);
lean_inc(v_ematchDiagSource_3672_);
lean_inc(v_generation_3668_);
lean_inc_ref(v_root_3657_);
v___y_3568_ = v_root_3657_;
v___y_3569_ = v_ctor_3664_;
v___y_3570_ = v_generation_3668_;
v___y_3571_ = v_ematchDiagSource_3672_;
v___y_3572_ = v_sTerms_3670_;
v___y_3573_ = v_mt_3669_;
v___y_3574_ = v_self_3655_;
v___y_3575_ = v___y_3624_;
v___y_3576_ = v___y_3623_;
v___y_3577_ = v___y_3622_;
v___y_3578_ = v___y_3614_;
v___y_3579_ = v___y_3616_;
v___y_3580_ = v___y_3619_;
v___y_3581_ = v_flipped_3661_;
v___y_3582_ = v___x_3676_;
v___y_3583_ = v___y_3627_;
v___y_3584_ = v___y_3608_;
v___y_3585_ = v_congr_3658_;
v___y_3586_ = v___y_3609_;
v___y_3587_ = v___y_3612_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v___y_3617_;
v___y_3590_ = v_proof_x3f_3660_;
v___y_3591_ = v___y_3620_;
v___y_3592_ = v___y_3607_;
v___y_3593_ = v___y_3625_;
v___y_3594_ = v___x_3631_;
v___y_3595_ = v_target_x3f_3659_;
v___y_3596_ = v___y_3613_;
v___y_3597_ = v_funCC_3671_;
v___y_3598_ = v_interpreted_3663_;
v___y_3599_ = v___y_3626_;
v___y_3600_ = v_idx_3667_;
v___y_3601_ = v___y_3618_;
v___y_3602_ = v___y_3621_;
v___y_3603_ = v_heqProofs_3666_;
v___y_3604_ = v_hasLambdas_3665_;
goto v___jp_3567_;
}
}
else
{
lean_dec(v___x_3631_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_dec(v___x_3631_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
v_a_3680_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3633_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3633_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
return v___x_3628_;
}
}
v___jp_3693_:
{
lean_object* v_self_3709_; lean_object* v_next_3710_; lean_object* v_size_3711_; uint8_t v_hasLambdas_3712_; uint8_t v_heqProofs_3713_; lean_object* v___x_3714_; 
v_self_3709_ = lean_ctor_get(v_lhsRoot_3436_, 0);
v_next_3710_ = lean_ctor_get(v_lhsRoot_3436_, 1);
v_size_3711_ = lean_ctor_get(v_lhsRoot_3436_, 6);
v_hasLambdas_3712_ = lean_ctor_get_uint8(v_lhsRoot_3436_, sizeof(void*)*12 + 3);
v_heqProofs_3713_ = lean_ctor_get_uint8(v_lhsRoot_3436_, sizeof(void*)*12 + 4);
v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3709_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v_root_3716_; lean_object* v___x_3717_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3714_, 1);
v_root_3716_ = lean_ctor_get(v_rhsNode_3435_, 2);
lean_inc_ref_n(v_root_3716_, 2);
lean_dec_ref(v_rhsNode_3435_);
lean_inc_ref(v_lhs_3432_);
v___x_3717_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3432_, v_root_3716_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_toCold_3718_; lean_object* v_options_3719_; uint8_t v_hasTrace_3720_; 
lean_dec_ref_known(v___x_3717_, 1);
v_toCold_3718_ = lean_ctor_get(v___y_3707_, 0);
v_options_3719_ = lean_ctor_get(v_toCold_3718_, 2);
v_hasTrace_3720_ = lean_ctor_get_uint8(v_options_3719_, sizeof(void*)*1);
if (v_hasTrace_3720_ == 0)
{
lean_inc_ref(v_next_3710_);
lean_inc_ref(v_self_3709_);
lean_inc(v_size_3711_);
v___y_3606_ = v_hasLambdas_3712_;
v___y_3607_ = v___y_3695_;
v___y_3608_ = v___y_3694_;
v___y_3609_ = v___y_3696_;
v___y_3610_ = v_size_3711_;
v___y_3611_ = v_fns_u2082_3698_;
v___y_3612_ = v_self_3709_;
v___y_3613_ = v_root_3716_;
v___y_3614_ = v_heqProofs_3713_;
v___y_3615_ = v___y_3697_;
v___y_3616_ = v_a_3715_;
v___y_3617_ = v_next_3710_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
goto v___jp_3605_;
}
else
{
lean_object* v_inheritedTraceOptions_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_inheritedTraceOptions_3721_ = lean_ctor_get(v_toCold_3718_, 11);
v___x_3722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3721_, v_options_3719_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_inc_ref(v_next_3710_);
lean_inc_ref(v_self_3709_);
lean_inc(v_size_3711_);
v___y_3606_ = v_hasLambdas_3712_;
v___y_3607_ = v___y_3695_;
v___y_3608_ = v___y_3694_;
v___y_3609_ = v___y_3696_;
v___y_3610_ = v_size_3711_;
v___y_3611_ = v_fns_u2082_3698_;
v___y_3612_ = v_self_3709_;
v___y_3613_ = v_root_3716_;
v___y_3614_ = v_heqProofs_3713_;
v___y_3615_ = v___y_3697_;
v___y_3616_ = v_a_3715_;
v___y_3617_ = v_next_3710_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_Meta_Grind_updateLastTag(v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3725_; 
lean_dec_ref_known(v___x_3724_, 1);
lean_inc_ref(v_lhs_3432_);
v___x_3725_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3432_, v___y_3699_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
lean_inc_ref(v_root_3716_);
v___x_3727_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3716_, v___y_3699_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = lean_st_ref_get(v___y_3699_);
lean_inc_ref(v_lhs_3432_);
v___x_3730_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3729_, v_lhs_3432_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___x_3729_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3732_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3731_, v___y_3699_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_a_3726_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v_a_3728_);
v___x_3737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v_a_3733_);
v___x_3740_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3692_, v___x_3739_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_dec_ref_known(v___x_3740_, 1);
lean_inc_ref(v_next_3710_);
lean_inc_ref(v_self_3709_);
lean_inc(v_size_3711_);
v___y_3606_ = v_hasLambdas_3712_;
v___y_3607_ = v___y_3695_;
v___y_3608_ = v___y_3694_;
v___y_3609_ = v___y_3696_;
v___y_3610_ = v_size_3711_;
v___y_3611_ = v_fns_u2082_3698_;
v___y_3612_ = v_self_3709_;
v___y_3613_ = v_root_3716_;
v___y_3614_ = v_heqProofs_3713_;
v___y_3615_ = v___y_3697_;
v___y_3616_ = v_a_3715_;
v___y_3617_ = v_next_3710_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
v___y_3625_ = v___y_3706_;
v___y_3626_ = v___y_3707_;
v___y_3627_ = v___y_3708_;
goto v___jp_3605_;
}
else
{
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
return v___x_3740_;
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_a_3728_);
lean_dec(v_a_3726_);
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
v_a_3741_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3732_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3732_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_a_3728_);
lean_dec(v_a_3726_);
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
v_a_3749_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3730_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3730_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3726_);
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
v_a_3757_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3727_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3727_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
v_a_3765_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3725_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3725_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
return v___x_3724_;
}
}
}
}
else
{
lean_dec_ref(v_root_3716_);
lean_dec(v_a_3715_);
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_lhs_3432_);
return v___x_3717_;
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_fns_u2082_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
v_a_3773_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3714_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3714_);
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
v___jp_3781_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v___x_3796_ = lean_array_get_size(v___y_3782_);
v___x_3797_ = lean_unsigned_to_nat(0u);
v___x_3798_ = lean_nat_dec_eq(v___x_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v_self_3799_; lean_object* v___x_3800_; 
v_self_3799_ = lean_ctor_get(v_lhsRoot_3436_, 0);
lean_inc_ref(v_self_3799_);
v___x_3800_ = l_Lean_Meta_Grind_getFnRoots(v_self_3799_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___y_3694_ = v_fns_u2081_3785_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v_fns_u2082_3698_ = v_a_3801_;
v___y_3699_ = v___y_3786_;
v___y_3700_ = v___y_3787_;
v___y_3701_ = v___y_3788_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
goto v___jp_3693_;
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_fns_u2081_3785_);
lean_dec_ref(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
v_a_3802_ = lean_ctor_get(v___x_3800_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3800_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3800_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3800_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; 
v___x_3810_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3694_ = v_fns_u2081_3785_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v_fns_u2082_3698_ = v___x_3810_;
v___y_3699_ = v___y_3786_;
v___y_3700_ = v___y_3787_;
v___y_3701_ = v___y_3788_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
goto v___jp_3693_;
}
}
v___jp_3811_:
{
lean_object* v___x_3822_; 
lean_inc_ref(v_lhs_3432_);
v___x_3822_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3432_, v___y_3812_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3890_; 
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; 
v_unused_3891_ = lean_ctor_get(v___x_3822_, 0);
lean_dec(v_unused_3891_);
v___x_3824_ = v___x_3822_;
v_isShared_3825_ = v_isSharedCheck_3890_;
goto v_resetjp_3823_;
}
else
{
lean_dec(v___x_3822_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3890_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_self_3826_; lean_object* v_next_3827_; lean_object* v_root_3828_; lean_object* v_congr_3829_; lean_object* v_size_3830_; uint8_t v_interpreted_3831_; uint8_t v_ctor_3832_; uint8_t v_hasLambdas_3833_; uint8_t v_heqProofs_3834_; lean_object* v_idx_3835_; lean_object* v_generation_3836_; lean_object* v_mt_3837_; lean_object* v_sTerms_3838_; uint8_t v_funCC_3839_; lean_object* v_ematchDiagSource_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3887_; 
v_self_3826_ = lean_ctor_get(v_lhsNode_3434_, 0);
v_next_3827_ = lean_ctor_get(v_lhsNode_3434_, 1);
v_root_3828_ = lean_ctor_get(v_lhsNode_3434_, 2);
v_congr_3829_ = lean_ctor_get(v_lhsNode_3434_, 3);
v_size_3830_ = lean_ctor_get(v_lhsNode_3434_, 6);
v_interpreted_3831_ = lean_ctor_get_uint8(v_lhsNode_3434_, sizeof(void*)*12 + 1);
v_ctor_3832_ = lean_ctor_get_uint8(v_lhsNode_3434_, sizeof(void*)*12 + 2);
v_hasLambdas_3833_ = lean_ctor_get_uint8(v_lhsNode_3434_, sizeof(void*)*12 + 3);
v_heqProofs_3834_ = lean_ctor_get_uint8(v_lhsNode_3434_, sizeof(void*)*12 + 4);
v_idx_3835_ = lean_ctor_get(v_lhsNode_3434_, 7);
v_generation_3836_ = lean_ctor_get(v_lhsNode_3434_, 8);
v_mt_3837_ = lean_ctor_get(v_lhsNode_3434_, 9);
v_sTerms_3838_ = lean_ctor_get(v_lhsNode_3434_, 10);
v_funCC_3839_ = lean_ctor_get_uint8(v_lhsNode_3434_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3840_ = lean_ctor_get(v_lhsNode_3434_, 11);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_lhsNode_3434_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3888_ = lean_ctor_get(v_lhsNode_3434_, 5);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_lhsNode_3434_, 4);
lean_dec(v_unused_3889_);
v___x_3842_ = v_lhsNode_3434_;
v_isShared_3843_ = v_isSharedCheck_3887_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_ematchDiagSource_3840_);
lean_inc(v_sTerms_3838_);
lean_inc(v_mt_3837_);
lean_inc(v_generation_3836_);
lean_inc(v_idx_3835_);
lean_inc(v_size_3830_);
lean_inc(v_congr_3829_);
lean_inc(v_root_3828_);
lean_inc(v_next_3827_);
lean_inc(v_self_3826_);
lean_dec(v_lhsNode_3434_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3887_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set_tag(v___x_3824_, 1);
lean_ctor_set(v___x_3824_, 0, v_rhs_3433_);
v___x_3845_ = v___x_3824_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_rhs_3433_);
v___x_3845_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3848_; 
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_proof_3430_);
lean_inc_ref(v_root_3828_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 5, v___x_3846_);
lean_ctor_set(v___x_3842_, 4, v___x_3845_);
v___x_3848_ = v___x_3842_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_self_3826_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_next_3827_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_root_3828_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_congr_3829_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3885_, 5, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3885_, 6, v_size_3830_);
lean_ctor_set(v_reuseFailAlloc_3885_, 7, v_idx_3835_);
lean_ctor_set(v_reuseFailAlloc_3885_, 8, v_generation_3836_);
lean_ctor_set(v_reuseFailAlloc_3885_, 9, v_mt_3837_);
lean_ctor_set(v_reuseFailAlloc_3885_, 10, v_sTerms_3838_);
lean_ctor_set(v_reuseFailAlloc_3885_, 11, v_ematchDiagSource_3840_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*12 + 1, v_interpreted_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*12 + 2, v_ctor_3832_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*12 + 3, v_hasLambdas_3833_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*12 + 4, v_heqProofs_3834_);
lean_ctor_set_uint8(v_reuseFailAlloc_3885_, sizeof(void*)*12 + 5, v_funCC_3839_);
v___x_3848_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3849_; 
lean_ctor_set_uint8(v___x_3848_, sizeof(void*)*12, v_flipped_3438_);
lean_inc_ref(v_lhs_3432_);
v___x_3849_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3432_, v___x_3848_, v___y_3812_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v___x_3850_; 
lean_dec_ref_known(v___x_3849_, 1);
v___x_3850_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3436_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3437_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = lean_array_get_size(v_a_3851_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_nat_dec_eq(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v_self_3857_; lean_object* v___x_3858_; 
v_self_3857_ = lean_ctor_get(v_rhsRoot_3437_, 0);
lean_inc_ref(v_self_3857_);
v___x_3858_ = l_Lean_Meta_Grind_getFnRoots(v_self_3857_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v___y_3782_ = v_a_3853_;
v___y_3783_ = v_a_3851_;
v___y_3784_ = v_root_3828_;
v_fns_u2081_3785_ = v_a_3859_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
goto v___jp_3781_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_a_3853_);
lean_dec(v_a_3851_);
lean_dec_ref(v_root_3828_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
v_a_3860_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3858_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3782_ = v_a_3853_;
v___y_3783_ = v_a_3851_;
v___y_3784_ = v_root_3828_;
v_fns_u2081_3785_ = v___x_3868_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
goto v___jp_3781_;
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec(v_a_3851_);
lean_dec_ref(v_root_3828_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
v_a_3869_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3852_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3852_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v_root_3828_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
v_a_3877_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3850_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3850_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_dec_ref(v_root_3828_);
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhs_3432_);
return v___x_3849_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3437_);
lean_dec_ref(v_lhsRoot_3436_);
lean_dec_ref(v_rhsNode_3435_);
lean_dec_ref(v_lhsNode_3434_);
lean_dec_ref(v_rhs_3433_);
lean_dec_ref(v_lhs_3432_);
lean_dec_ref(v_proof_3430_);
return v___x_3822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3921_ = _args[0];
lean_object* v_isHEq_3922_ = _args[1];
lean_object* v_lhs_3923_ = _args[2];
lean_object* v_rhs_3924_ = _args[3];
lean_object* v_lhsNode_3925_ = _args[4];
lean_object* v_rhsNode_3926_ = _args[5];
lean_object* v_lhsRoot_3927_ = _args[6];
lean_object* v_rhsRoot_3928_ = _args[7];
lean_object* v_flipped_3929_ = _args[8];
lean_object* v_a_3930_ = _args[9];
lean_object* v_a_3931_ = _args[10];
lean_object* v_a_3932_ = _args[11];
lean_object* v_a_3933_ = _args[12];
lean_object* v_a_3934_ = _args[13];
lean_object* v_a_3935_ = _args[14];
lean_object* v_a_3936_ = _args[15];
lean_object* v_a_3937_ = _args[16];
lean_object* v_a_3938_ = _args[17];
lean_object* v_a_3939_ = _args[18];
lean_object* v_a_3940_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3941_; uint8_t v_flipped_boxed_3942_; lean_object* v_res_3943_; 
v_isHEq_boxed_3941_ = lean_unbox(v_isHEq_3922_);
v_flipped_boxed_3942_ = lean_unbox(v_flipped_3929_);
v_res_3943_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3921_, v_isHEq_boxed_3941_, v_lhs_3923_, v_rhs_3924_, v_lhsNode_3925_, v_rhsNode_3926_, v_lhsRoot_3927_, v_rhsRoot_3928_, v_flipped_boxed_3942_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec(v_a_3930_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3944_, lean_object* v_as_x27_3945_, lean_object* v_b_3946_, lean_object* v_a_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3945_, v_b_3946_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3960_, lean_object* v_as_x27_3961_, lean_object* v_b_3962_, lean_object* v_a_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3960_, v_as_x27_3961_, v_b_3962_, v_a_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v_as_x27_3961_);
lean_dec(v_as_3960_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3976_, lean_object* v_as_x27_3977_, lean_object* v_b_3978_, lean_object* v_a_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3977_, v_b_3978_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3992_, lean_object* v_as_x27_3993_, lean_object* v_b_3994_, lean_object* v_a_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3992_, v_as_x27_3993_, v_b_3994_, v_a_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec(v_as_x27_3993_);
lean_dec(v_as_3992_);
return v_res_4007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4010_ = l_Lean_stringToMessageData(v___x_4009_);
return v___x_4010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4016_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4017_ = l_Lean_Name_append(v___x_4016_, v___x_4015_);
return v___x_4017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4020_ = l_Lean_stringToMessageData(v___x_4019_);
return v___x_4020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4023_ = l_Lean_stringToMessageData(v___x_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4024_, lean_object* v_rhs_4025_, lean_object* v_proof_4026_, uint8_t v_isHEq_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_st_ref_get(v_a_4028_);
lean_inc_ref(v_lhs_4024_);
v___x_4043_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4042_, v_lhs_4024_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v___x_4042_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = lean_st_ref_get(v_a_4028_);
lean_inc_ref(v_rhs_4025_);
v___x_4046_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4045_, v_rhs_4025_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v___x_4045_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v_root_4048_; lean_object* v_root_4049_; size_t v___x_4050_; size_t v___x_4051_; uint8_t v___x_4052_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4046_, 1);
v_root_4048_ = lean_ctor_get(v_a_4044_, 2);
v_root_4049_ = lean_ctor_get(v_a_4047_, 2);
v___x_4050_ = lean_ptr_addr(v_root_4048_);
v___x_4051_ = lean_ptr_addr(v_root_4049_);
v___x_4052_ = lean_usize_dec_eq(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v_toCold_4053_; lean_object* v_options_4054_; lean_object* v_inheritedTraceOptions_4055_; uint8_t v_hasTrace_4056_; uint8_t v___x_4057_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4123_; lean_object* v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4153_; uint8_t v___y_4154_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; uint8_t v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; uint8_t v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; uint8_t v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; uint8_t v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; uint8_t v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; uint8_t v___y_4209_; lean_object* v___y_4210_; lean_object* v_size_4211_; uint8_t v_interpreted_4212_; uint8_t v_ctor_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v___y_4224_; lean_object* v___y_4225_; uint8_t v_ctor_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; uint8_t v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4243_; lean_object* v___y_4244_; uint8_t v_valueInconsistency_4245_; uint8_t v_trueEqFalse_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4276_; lean_object* v___y_4277_; uint8_t v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; 
v_toCold_4053_ = lean_ctor_get(v_a_4036_, 0);
v_options_4054_ = lean_ctor_get(v_toCold_4053_, 2);
v_inheritedTraceOptions_4055_ = lean_ctor_get(v_toCold_4053_, 11);
v_hasTrace_4056_ = lean_ctor_get_uint8(v_options_4054_, sizeof(void*)*1);
v___x_4057_ = 1;
if (v_hasTrace_4056_ == 0)
{
v___y_4303_ = v_a_4028_;
v___y_4304_ = v_a_4029_;
v___y_4305_ = v_a_4030_;
v___y_4306_ = v_a_4031_;
v___y_4307_ = v_a_4032_;
v___y_4308_ = v_a_4033_;
v___y_4309_ = v_a_4034_;
v___y_4310_ = v_a_4035_;
v___y_4311_ = v_a_4036_;
v___y_4312_ = v_a_4037_;
goto v___jp_4302_;
}
else
{
lean_object* v___x_4346_; lean_object* v_____do__lift_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v___x_4346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4362_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4055_, v_options_4054_, v___x_4361_);
if (v___x_4362_ == 0)
{
v___y_4303_ = v_a_4028_;
v___y_4304_ = v_a_4029_;
v___y_4305_ = v_a_4030_;
v___y_4306_ = v_a_4031_;
v___y_4307_ = v_a_4032_;
v___y_4308_ = v_a_4033_;
v___y_4309_ = v_a_4034_;
v___y_4310_ = v_a_4035_;
v___y_4311_ = v_a_4036_;
v___y_4312_ = v_a_4037_;
goto v___jp_4302_;
}
else
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_Meta_Grind_updateLastTag(v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_dec_ref_known(v___x_4363_, 1);
if (v_isHEq_4027_ == 0)
{
lean_object* v___x_4364_; 
lean_inc_ref(v_rhs_4025_);
lean_inc_ref(v_lhs_4024_);
v___x_4364_ = l_Lean_Meta_mkEq(v_lhs_4024_, v_rhs_4025_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v_____do__lift_4348_ = v_a_4365_;
v___y_4349_ = v_a_4028_;
v___y_4350_ = v_a_4029_;
v___y_4351_ = v_a_4030_;
v___y_4352_ = v_a_4031_;
v___y_4353_ = v_a_4032_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
goto v___jp_4347_;
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4366_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4364_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4364_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v___x_4374_; 
lean_inc_ref(v_rhs_4025_);
lean_inc_ref(v_lhs_4024_);
v___x_4374_ = l_Lean_Meta_mkHEq(v_lhs_4024_, v_rhs_4025_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v_____do__lift_4348_ = v_a_4375_;
v___y_4349_ = v_a_4028_;
v___y_4350_ = v_a_4029_;
v___y_4351_ = v_a_4030_;
v___y_4352_ = v_a_4031_;
v___y_4353_ = v_a_4032_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
goto v___jp_4347_;
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4376_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4374_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4374_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
else
{
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
return v___x_4363_;
}
}
v___jp_4347_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = l_Lean_MessageData_ofExpr(v_____do__lift_4348_);
v___x_4360_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4346_, v___x_4359_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_dec_ref_known(v___x_4360_, 1);
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
v___y_4305_ = v___y_4351_;
v___y_4306_ = v___y_4352_;
v___y_4307_ = v___y_4353_;
v___y_4308_ = v___y_4354_;
v___y_4309_ = v___y_4355_;
v___y_4310_ = v___y_4356_;
v___y_4311_ = v___y_4357_;
v___y_4312_ = v___y_4358_;
goto v___jp_4302_;
}
else
{
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
return v___x_4360_;
}
}
}
v___jp_4058_:
{
lean_object* v_toCold_4069_; lean_object* v_options_4070_; uint8_t v_hasTrace_4071_; 
v_toCold_4069_ = lean_ctor_get(v___y_4067_, 0);
v_options_4070_ = lean_ctor_get(v_toCold_4069_, 2);
v_hasTrace_4071_ = lean_ctor_get_uint8(v_options_4070_, sizeof(void*)*1);
if (v_hasTrace_4071_ == 0)
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_Meta_Grind_checkInvariants(v___x_4052_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4072_;
}
else
{
lean_object* v_inheritedTraceOptions_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v_inheritedTraceOptions_4073_ = lean_ctor_get(v_toCold_4069_, 11);
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4073_, v_options_4070_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Meta_Grind_checkInvariants(v___x_4052_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4077_;
}
else
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Meta_Grind_updateLastTag(v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_dec_ref_known(v___x_4078_, 1);
v___x_4079_ = lean_st_ref_get(v___y_4059_);
v___x_4080_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4079_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___x_4079_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
lean_ctor_set(v___x_4083_, 1, v_a_4081_);
v___x_4084_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4074_, v___x_4083_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4085_; 
lean_dec_ref_known(v___x_4084_, 1);
v___x_4085_ = l_Lean_Meta_Grind_checkInvariants(v___x_4052_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4085_;
}
else
{
return v___x_4084_;
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
v_a_4086_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4080_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4080_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
return v___x_4078_;
}
}
}
}
v___jp_4094_:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4098_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; uint8_t v___x_4110_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___x_4108_, 1);
v___x_4110_ = lean_unbox(v_a_4109_);
lean_dec(v_a_4109_);
if (v___x_4110_ == 0)
{
if (v___y_4097_ == 0)
{
lean_dec_ref(v___y_4096_);
lean_dec_ref(v___y_4095_);
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
goto v___jp_4058_;
}
else
{
lean_object* v_self_4111_; lean_object* v_self_4112_; lean_object* v___x_4113_; 
v_self_4111_ = lean_ctor_get(v___y_4096_, 0);
lean_inc_ref(v_self_4111_);
lean_dec_ref(v___y_4096_);
v_self_4112_ = lean_ctor_get(v___y_4095_, 0);
lean_inc_ref(v_self_4112_);
lean_dec_ref(v___y_4095_);
v___x_4113_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4111_, v_self_4112_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_dec_ref_known(v___x_4113_, 1);
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
goto v___jp_4058_;
}
else
{
return v___x_4113_;
}
}
}
else
{
lean_dec_ref(v___y_4096_);
lean_dec_ref(v___y_4095_);
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
goto v___jp_4058_;
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec_ref(v___y_4096_);
lean_dec_ref(v___y_4095_);
v_a_4114_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4108_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4108_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
v___jp_4122_:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4126_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; uint8_t v___x_4138_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v___x_4138_ = lean_unbox(v_a_4137_);
lean_dec(v_a_4137_);
if (v___x_4138_ == 0)
{
uint8_t v_ctor_4139_; 
v_ctor_4139_ = lean_ctor_get_uint8(v___y_4124_, sizeof(void*)*12 + 2);
if (v_ctor_4139_ == 0)
{
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
v___y_4098_ = v___y_4126_;
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
goto v___jp_4094_;
}
else
{
uint8_t v_ctor_4140_; 
v_ctor_4140_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*12 + 2);
if (v_ctor_4140_ == 0)
{
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
v___y_4098_ = v___y_4126_;
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
goto v___jp_4094_;
}
else
{
lean_object* v_self_4141_; lean_object* v_self_4142_; lean_object* v___x_4143_; 
v_self_4141_ = lean_ctor_get(v___y_4124_, 0);
v_self_4142_ = lean_ctor_get(v___y_4123_, 0);
lean_inc_ref(v_self_4142_);
lean_inc_ref(v_self_4141_);
v___x_4143_ = l_Lean_Meta_Grind_propagateCtor(v_self_4141_, v_self_4142_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec_ref_known(v___x_4143_, 1);
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
v___y_4098_ = v___y_4126_;
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
goto v___jp_4094_;
}
else
{
lean_dec_ref(v___y_4124_);
lean_dec_ref(v___y_4123_);
return v___x_4143_;
}
}
}
}
else
{
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
v___y_4098_ = v___y_4126_;
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
goto v___jp_4094_;
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___y_4124_);
lean_dec_ref(v___y_4123_);
v_a_4144_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4136_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4136_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
v___jp_4152_:
{
if (v___y_4154_ == 0)
{
v___y_4123_ = v___y_4153_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4160_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_dec_ref_known(v___x_4167_, 1);
v___y_4123_ = v___y_4153_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4160_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
goto v___jp_4122_;
}
else
{
lean_dec_ref(v___y_4155_);
lean_dec_ref(v___y_4153_);
return v___x_4167_;
}
}
}
v___jp_4168_:
{
lean_object* v___x_4183_; 
lean_inc_ref(v___y_4173_);
lean_inc_ref(v___y_4178_);
v___x_4183_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4026_, v_isHEq_4027_, v_rhs_4025_, v_lhs_4024_, v_a_4047_, v_a_4044_, v___y_4178_, v___y_4173_, v___x_4057_, v___y_4179_, v___y_4180_, v___y_4174_, v___y_4169_, v___y_4181_, v___y_4182_, v___y_4170_, v___y_4175_, v___y_4171_, v___y_4176_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_dec_ref_known(v___x_4183_, 1);
v___y_4153_ = v___y_4178_;
v___y_4154_ = v___y_4172_;
v___y_4155_ = v___y_4173_;
v___y_4156_ = v___y_4177_;
v___y_4157_ = v___y_4179_;
v___y_4158_ = v___y_4180_;
v___y_4159_ = v___y_4174_;
v___y_4160_ = v___y_4169_;
v___y_4161_ = v___y_4181_;
v___y_4162_ = v___y_4182_;
v___y_4163_ = v___y_4170_;
v___y_4164_ = v___y_4175_;
v___y_4165_ = v___y_4171_;
v___y_4166_ = v___y_4176_;
goto v___jp_4152_;
}
else
{
lean_dec_ref(v___y_4178_);
lean_dec_ref(v___y_4173_);
return v___x_4183_;
}
}
v___jp_4184_:
{
lean_object* v___x_4199_; 
lean_inc_ref(v___y_4194_);
lean_inc_ref(v___y_4189_);
v___x_4199_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4026_, v_isHEq_4027_, v_lhs_4024_, v_rhs_4025_, v_a_4044_, v_a_4047_, v___y_4189_, v___y_4194_, v___x_4052_, v___y_4195_, v___y_4196_, v___y_4190_, v___y_4185_, v___y_4197_, v___y_4198_, v___y_4186_, v___y_4191_, v___y_4187_, v___y_4192_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_dec_ref_known(v___x_4199_, 1);
v___y_4153_ = v___y_4194_;
v___y_4154_ = v___y_4188_;
v___y_4155_ = v___y_4189_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4195_;
v___y_4158_ = v___y_4196_;
v___y_4159_ = v___y_4190_;
v___y_4160_ = v___y_4185_;
v___y_4161_ = v___y_4197_;
v___y_4162_ = v___y_4198_;
v___y_4163_ = v___y_4186_;
v___y_4164_ = v___y_4191_;
v___y_4165_ = v___y_4187_;
v___y_4166_ = v___y_4192_;
goto v___jp_4152_;
}
else
{
lean_dec_ref(v___y_4194_);
lean_dec_ref(v___y_4189_);
return v___x_4199_;
}
}
v___jp_4200_:
{
lean_object* v_size_4218_; uint8_t v___x_4219_; 
v_size_4218_ = lean_ctor_get(v___y_4205_, 6);
v___x_4219_ = lean_nat_dec_lt(v_size_4211_, v_size_4218_);
lean_dec(v_size_4211_);
if (v___x_4219_ == 0)
{
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
goto v___jp_4184_;
}
else
{
if (v_interpreted_4212_ == 0)
{
if (v_ctor_4213_ == 0)
{
v___y_4169_ = v___y_4201_;
v___y_4170_ = v___y_4202_;
v___y_4171_ = v___y_4203_;
v___y_4172_ = v___y_4204_;
v___y_4173_ = v___y_4205_;
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4208_;
v___y_4177_ = v___y_4209_;
v___y_4178_ = v___y_4210_;
v___y_4179_ = v___y_4214_;
v___y_4180_ = v___y_4215_;
v___y_4181_ = v___y_4216_;
v___y_4182_ = v___y_4217_;
goto v___jp_4168_;
}
else
{
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
goto v___jp_4184_;
}
}
else
{
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
goto v___jp_4184_;
}
}
}
v___jp_4220_:
{
if (v_ctor_4226_ == 0)
{
lean_object* v_size_4236_; uint8_t v_interpreted_4237_; uint8_t v_ctor_4238_; 
v_size_4236_ = lean_ctor_get(v___y_4231_, 6);
lean_inc(v_size_4236_);
v_interpreted_4237_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*12 + 1);
v_ctor_4238_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*12 + 2);
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___y_4225_;
v___y_4206_ = v___y_4227_;
v___y_4207_ = v___y_4228_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4230_;
v___y_4210_ = v___y_4231_;
v_size_4211_ = v_size_4236_;
v_interpreted_4212_ = v_interpreted_4237_;
v_ctor_4213_ = v_ctor_4238_;
v___y_4214_ = v___y_4232_;
v___y_4215_ = v___y_4233_;
v___y_4216_ = v___y_4234_;
v___y_4217_ = v___y_4235_;
goto v___jp_4200_;
}
else
{
uint8_t v_ctor_4239_; 
v_ctor_4239_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*12 + 2);
if (v_ctor_4239_ == 0)
{
v___y_4169_ = v___y_4221_;
v___y_4170_ = v___y_4222_;
v___y_4171_ = v___y_4223_;
v___y_4172_ = v___y_4224_;
v___y_4173_ = v___y_4225_;
v___y_4174_ = v___y_4227_;
v___y_4175_ = v___y_4228_;
v___y_4176_ = v___y_4229_;
v___y_4177_ = v___y_4230_;
v___y_4178_ = v___y_4231_;
v___y_4179_ = v___y_4232_;
v___y_4180_ = v___y_4233_;
v___y_4181_ = v___y_4234_;
v___y_4182_ = v___y_4235_;
goto v___jp_4168_;
}
else
{
lean_object* v_size_4240_; uint8_t v_interpreted_4241_; 
v_size_4240_ = lean_ctor_get(v___y_4231_, 6);
lean_inc(v_size_4240_);
v_interpreted_4241_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*12 + 1);
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___y_4225_;
v___y_4206_ = v___y_4227_;
v___y_4207_ = v___y_4228_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4230_;
v___y_4210_ = v___y_4231_;
v_size_4211_ = v_size_4240_;
v_interpreted_4212_ = v_interpreted_4241_;
v_ctor_4213_ = v_ctor_4239_;
v___y_4214_ = v___y_4232_;
v___y_4215_ = v___y_4233_;
v___y_4216_ = v___y_4234_;
v___y_4217_ = v___y_4235_;
goto v___jp_4200_;
}
}
}
v___jp_4242_:
{
uint8_t v_interpreted_4257_; 
v_interpreted_4257_ = lean_ctor_get_uint8(v___y_4244_, sizeof(void*)*12 + 1);
if (v_interpreted_4257_ == 0)
{
uint8_t v_ctor_4258_; 
v_ctor_4258_ = lean_ctor_get_uint8(v___y_4244_, sizeof(void*)*12 + 2);
v___y_4221_ = v___y_4250_;
v___y_4222_ = v___y_4253_;
v___y_4223_ = v___y_4255_;
v___y_4224_ = v_trueEqFalse_4246_;
v___y_4225_ = v___y_4244_;
v_ctor_4226_ = v_ctor_4258_;
v___y_4227_ = v___y_4249_;
v___y_4228_ = v___y_4254_;
v___y_4229_ = v___y_4256_;
v___y_4230_ = v_valueInconsistency_4245_;
v___y_4231_ = v___y_4243_;
v___y_4232_ = v___y_4247_;
v___y_4233_ = v___y_4248_;
v___y_4234_ = v___y_4251_;
v___y_4235_ = v___y_4252_;
goto v___jp_4220_;
}
else
{
uint8_t v_interpreted_4259_; 
v_interpreted_4259_ = lean_ctor_get_uint8(v___y_4243_, sizeof(void*)*12 + 1);
if (v_interpreted_4259_ == 0)
{
v___y_4169_ = v___y_4250_;
v___y_4170_ = v___y_4253_;
v___y_4171_ = v___y_4255_;
v___y_4172_ = v_trueEqFalse_4246_;
v___y_4173_ = v___y_4244_;
v___y_4174_ = v___y_4249_;
v___y_4175_ = v___y_4254_;
v___y_4176_ = v___y_4256_;
v___y_4177_ = v_valueInconsistency_4245_;
v___y_4178_ = v___y_4243_;
v___y_4179_ = v___y_4247_;
v___y_4180_ = v___y_4248_;
v___y_4181_ = v___y_4251_;
v___y_4182_ = v___y_4252_;
goto v___jp_4168_;
}
else
{
uint8_t v_ctor_4260_; 
v_ctor_4260_ = lean_ctor_get_uint8(v___y_4244_, sizeof(void*)*12 + 2);
v___y_4221_ = v___y_4250_;
v___y_4222_ = v___y_4253_;
v___y_4223_ = v___y_4255_;
v___y_4224_ = v_trueEqFalse_4246_;
v___y_4225_ = v___y_4244_;
v_ctor_4226_ = v_ctor_4260_;
v___y_4227_ = v___y_4249_;
v___y_4228_ = v___y_4254_;
v___y_4229_ = v___y_4256_;
v___y_4230_ = v_valueInconsistency_4245_;
v___y_4231_ = v___y_4243_;
v___y_4232_ = v___y_4247_;
v___y_4233_ = v___y_4248_;
v___y_4234_ = v___y_4251_;
v___y_4235_ = v___y_4252_;
goto v___jp_4220_;
}
}
}
v___jp_4261_:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4272_, v___y_4267_, v___y_4273_, v___y_4266_, v___y_4263_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_dec_ref_known(v___x_4274_, 1);
v___y_4243_ = v___y_4269_;
v___y_4244_ = v___y_4265_;
v_valueInconsistency_4245_ = v___x_4052_;
v_trueEqFalse_4246_ = v___x_4057_;
v___y_4247_ = v___y_4272_;
v___y_4248_ = v___y_4270_;
v___y_4249_ = v___y_4271_;
v___y_4250_ = v___y_4268_;
v___y_4251_ = v___y_4264_;
v___y_4252_ = v___y_4262_;
v___y_4253_ = v___y_4267_;
v___y_4254_ = v___y_4273_;
v___y_4255_ = v___y_4266_;
v___y_4256_ = v___y_4263_;
goto v___jp_4242_;
}
else
{
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4265_);
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
return v___x_4274_;
}
}
v___jp_4275_:
{
if (v___y_4278_ == 0)
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Meta_Grind_hasSameType(v___y_4277_, v___y_4280_, v___y_4284_, v___y_4290_, v___y_4283_, v___y_4279_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; uint8_t v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = lean_unbox(v_a_4292_);
lean_dec(v_a_4292_);
if (v___x_4293_ == 0)
{
v___y_4243_ = v___y_4286_;
v___y_4244_ = v___y_4281_;
v_valueInconsistency_4245_ = v___x_4052_;
v_trueEqFalse_4246_ = v___x_4052_;
v___y_4247_ = v___y_4289_;
v___y_4248_ = v___y_4287_;
v___y_4249_ = v___y_4288_;
v___y_4250_ = v___y_4285_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4276_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4279_;
goto v___jp_4242_;
}
else
{
v___y_4243_ = v___y_4286_;
v___y_4244_ = v___y_4281_;
v_valueInconsistency_4245_ = v___x_4057_;
v_trueEqFalse_4246_ = v___x_4052_;
v___y_4247_ = v___y_4289_;
v___y_4248_ = v___y_4287_;
v___y_4249_ = v___y_4288_;
v___y_4250_ = v___y_4285_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4276_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4279_;
goto v___jp_4242_;
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4281_);
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4294_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4291_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4291_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_dec_ref(v___y_4280_);
lean_dec_ref(v___y_4277_);
v___y_4243_ = v___y_4286_;
v___y_4244_ = v___y_4281_;
v_valueInconsistency_4245_ = v___x_4057_;
v_trueEqFalse_4246_ = v___x_4052_;
v___y_4247_ = v___y_4289_;
v___y_4248_ = v___y_4287_;
v___y_4249_ = v___y_4288_;
v___y_4250_ = v___y_4285_;
v___y_4251_ = v___y_4282_;
v___y_4252_ = v___y_4276_;
v___y_4253_ = v___y_4284_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4283_;
v___y_4256_ = v___y_4279_;
goto v___jp_4242_;
}
}
v___jp_4302_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_st_ref_get(v___y_4303_);
lean_inc_ref(v_root_4048_);
v___x_4314_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4313_, v_root_4048_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___x_4313_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = lean_st_ref_get(v___y_4303_);
lean_inc_ref(v_root_4049_);
v___x_4317_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4316_, v_root_4049_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___x_4316_);
if (lean_obj_tag(v___x_4317_) == 0)
{
uint8_t v_interpreted_4318_; 
v_interpreted_4318_ = lean_ctor_get_uint8(v_a_4315_, sizeof(void*)*12 + 1);
if (v_interpreted_4318_ == 0)
{
lean_object* v_a_4319_; uint8_t v_ctor_4320_; 
v_a_4319_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4317_, 1);
v_ctor_4320_ = lean_ctor_get_uint8(v_a_4315_, sizeof(void*)*12 + 2);
v___y_4221_ = v___y_4306_;
v___y_4222_ = v___y_4309_;
v___y_4223_ = v___y_4311_;
v___y_4224_ = v___x_4052_;
v___y_4225_ = v_a_4315_;
v_ctor_4226_ = v_ctor_4320_;
v___y_4227_ = v___y_4305_;
v___y_4228_ = v___y_4310_;
v___y_4229_ = v___y_4312_;
v___y_4230_ = v___x_4052_;
v___y_4231_ = v_a_4319_;
v___y_4232_ = v___y_4303_;
v___y_4233_ = v___y_4304_;
v___y_4234_ = v___y_4307_;
v___y_4235_ = v___y_4308_;
goto v___jp_4220_;
}
else
{
lean_object* v_a_4321_; uint8_t v_interpreted_4322_; 
v_a_4321_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4317_, 1);
v_interpreted_4322_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 1);
if (v_interpreted_4322_ == 0)
{
v___y_4169_ = v___y_4306_;
v___y_4170_ = v___y_4309_;
v___y_4171_ = v___y_4311_;
v___y_4172_ = v___x_4052_;
v___y_4173_ = v_a_4315_;
v___y_4174_ = v___y_4305_;
v___y_4175_ = v___y_4310_;
v___y_4176_ = v___y_4312_;
v___y_4177_ = v___x_4052_;
v___y_4178_ = v_a_4321_;
v___y_4179_ = v___y_4303_;
v___y_4180_ = v___y_4304_;
v___y_4181_ = v___y_4307_;
v___y_4182_ = v___y_4308_;
goto v___jp_4168_;
}
else
{
lean_object* v_self_4323_; uint8_t v_ctor_4324_; uint8_t v_heqProofs_4325_; lean_object* v_self_4326_; uint8_t v_heqProofs_4327_; uint8_t v___x_4328_; 
v_self_4323_ = lean_ctor_get(v_a_4315_, 0);
v_ctor_4324_ = lean_ctor_get_uint8(v_a_4315_, sizeof(void*)*12 + 2);
v_heqProofs_4325_ = lean_ctor_get_uint8(v_a_4315_, sizeof(void*)*12 + 4);
v_self_4326_ = lean_ctor_get(v_a_4321_, 0);
v_heqProofs_4327_ = lean_ctor_get_uint8(v_a_4321_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4048_);
v___x_4328_ = l_Lean_Expr_isTrue(v_root_4048_);
if (v___x_4328_ == 0)
{
uint8_t v___x_4329_; 
lean_inc_ref(v_root_4049_);
v___x_4329_ = l_Lean_Expr_isTrue(v_root_4049_);
if (v___x_4329_ == 0)
{
if (v_isHEq_4027_ == 0)
{
if (v_heqProofs_4325_ == 0)
{
if (v_heqProofs_4327_ == 0)
{
v___y_4221_ = v___y_4306_;
v___y_4222_ = v___y_4309_;
v___y_4223_ = v___y_4311_;
v___y_4224_ = v___x_4052_;
v___y_4225_ = v_a_4315_;
v_ctor_4226_ = v_ctor_4324_;
v___y_4227_ = v___y_4305_;
v___y_4228_ = v___y_4310_;
v___y_4229_ = v___y_4312_;
v___y_4230_ = v___x_4057_;
v___y_4231_ = v_a_4321_;
v___y_4232_ = v___y_4303_;
v___y_4233_ = v___y_4304_;
v___y_4234_ = v___y_4307_;
v___y_4235_ = v___y_4308_;
goto v___jp_4220_;
}
else
{
lean_inc_ref(v_self_4326_);
lean_inc_ref(v_self_4323_);
v___y_4276_ = v___y_4308_;
v___y_4277_ = v_self_4323_;
v___y_4278_ = v___x_4329_;
v___y_4279_ = v___y_4312_;
v___y_4280_ = v_self_4326_;
v___y_4281_ = v_a_4315_;
v___y_4282_ = v___y_4307_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4309_;
v___y_4285_ = v___y_4306_;
v___y_4286_ = v_a_4321_;
v___y_4287_ = v___y_4304_;
v___y_4288_ = v___y_4305_;
v___y_4289_ = v___y_4303_;
v___y_4290_ = v___y_4310_;
goto v___jp_4275_;
}
}
else
{
lean_inc_ref(v_self_4326_);
lean_inc_ref(v_self_4323_);
v___y_4276_ = v___y_4308_;
v___y_4277_ = v_self_4323_;
v___y_4278_ = v___x_4329_;
v___y_4279_ = v___y_4312_;
v___y_4280_ = v_self_4326_;
v___y_4281_ = v_a_4315_;
v___y_4282_ = v___y_4307_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4309_;
v___y_4285_ = v___y_4306_;
v___y_4286_ = v_a_4321_;
v___y_4287_ = v___y_4304_;
v___y_4288_ = v___y_4305_;
v___y_4289_ = v___y_4303_;
v___y_4290_ = v___y_4310_;
goto v___jp_4275_;
}
}
else
{
lean_inc_ref(v_self_4326_);
lean_inc_ref(v_self_4323_);
v___y_4276_ = v___y_4308_;
v___y_4277_ = v_self_4323_;
v___y_4278_ = v___x_4329_;
v___y_4279_ = v___y_4312_;
v___y_4280_ = v_self_4326_;
v___y_4281_ = v_a_4315_;
v___y_4282_ = v___y_4307_;
v___y_4283_ = v___y_4311_;
v___y_4284_ = v___y_4309_;
v___y_4285_ = v___y_4306_;
v___y_4286_ = v_a_4321_;
v___y_4287_ = v___y_4304_;
v___y_4288_ = v___y_4305_;
v___y_4289_ = v___y_4303_;
v___y_4290_ = v___y_4310_;
goto v___jp_4275_;
}
}
else
{
v___y_4262_ = v___y_4308_;
v___y_4263_ = v___y_4312_;
v___y_4264_ = v___y_4307_;
v___y_4265_ = v_a_4315_;
v___y_4266_ = v___y_4311_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4306_;
v___y_4269_ = v_a_4321_;
v___y_4270_ = v___y_4304_;
v___y_4271_ = v___y_4305_;
v___y_4272_ = v___y_4303_;
v___y_4273_ = v___y_4310_;
goto v___jp_4261_;
}
}
else
{
v___y_4262_ = v___y_4308_;
v___y_4263_ = v___y_4312_;
v___y_4264_ = v___y_4307_;
v___y_4265_ = v_a_4315_;
v___y_4266_ = v___y_4311_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4306_;
v___y_4269_ = v_a_4321_;
v___y_4270_ = v___y_4304_;
v___y_4271_ = v___y_4305_;
v___y_4272_ = v___y_4303_;
v___y_4273_ = v___y_4310_;
goto v___jp_4261_;
}
}
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_a_4315_);
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4330_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4317_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4317_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4338_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4314_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4314_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
}
else
{
lean_object* v_toCold_4384_; lean_object* v_options_4385_; uint8_t v_hasTrace_4386_; 
lean_dec(v_a_4047_);
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
v_toCold_4384_ = lean_ctor_get(v_a_4036_, 0);
v_options_4385_ = lean_ctor_get(v_toCold_4384_, 2);
v_hasTrace_4386_ = lean_ctor_get_uint8(v_options_4385_, sizeof(void*)*1);
if (v_hasTrace_4386_ == 0)
{
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
goto v___jp_4039_;
}
else
{
lean_object* v_inheritedTraceOptions_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; uint8_t v___x_4390_; 
v_inheritedTraceOptions_4387_ = lean_ctor_get(v_toCold_4384_, 11);
v___x_4388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4387_, v_options_4385_, v___x_4389_);
if (v___x_4390_ == 0)
{
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
goto v___jp_4039_;
}
else
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Meta_Grind_updateLastTag(v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v___x_4392_; 
lean_dec_ref_known(v___x_4391_, 1);
v___x_4392_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4024_, v_a_4028_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4025_, v_a_4028_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v_a_4393_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
lean_ctor_set(v___x_4398_, 1, v_a_4395_);
v___x_4399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4388_, v___x_4400_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_dec_ref_known(v___x_4401_, 1);
goto v___jp_4039_;
}
else
{
return v___x_4401_;
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_a_4393_);
v_a_4402_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4394_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4394_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec_ref(v_rhs_4025_);
v_a_4410_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4392_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4392_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
return v___x_4391_;
}
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v_a_4044_);
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4418_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4046_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4046_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec_ref(v_proof_4026_);
lean_dec_ref(v_rhs_4025_);
lean_dec_ref(v_lhs_4024_);
v_a_4426_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4043_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4043_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
v___jp_4039_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_box(0);
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
return v___x_4041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4434_, lean_object* v_rhs_4435_, lean_object* v_proof_4436_, lean_object* v_isHEq_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
uint8_t v_isHEq_boxed_4449_; lean_object* v_res_4450_; 
v_isHEq_boxed_4449_ = lean_unbox(v_isHEq_4437_);
v_res_4450_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4434_, v_rhs_4435_, v_proof_4436_, v_isHEq_boxed_4449_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
lean_dec(v_a_4439_);
lean_dec(v_a_4438_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4455_; lean_object* v_toGoalState_4456_; lean_object* v_mvarId_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4494_; 
v___x_4455_ = lean_st_ref_take(v_a_4453_);
v_toGoalState_4456_ = lean_ctor_get(v___x_4455_, 0);
v_mvarId_4457_ = lean_ctor_get(v___x_4455_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4459_ = v___x_4455_;
v_isShared_4460_ = v_isSharedCheck_4494_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_mvarId_4457_);
lean_inc(v_toGoalState_4456_);
lean_dec(v___x_4455_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4494_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_nextDeclIdx_4461_; lean_object* v_enodeMap_4462_; lean_object* v_exprs_4463_; lean_object* v_parents_4464_; lean_object* v_congrTable_4465_; lean_object* v_appMap_4466_; lean_object* v_indicesFound_4467_; lean_object* v_internalizing_4468_; uint8_t v_inconsistent_4469_; lean_object* v_nextIdx_4470_; lean_object* v_newRawFacts_4471_; lean_object* v_facts_4472_; lean_object* v_extThms_4473_; lean_object* v_ematch_4474_; lean_object* v_inj_4475_; lean_object* v_split_4476_; lean_object* v_clean_4477_; lean_object* v_sstates_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4492_; 
v_nextDeclIdx_4461_ = lean_ctor_get(v_toGoalState_4456_, 0);
v_enodeMap_4462_ = lean_ctor_get(v_toGoalState_4456_, 1);
v_exprs_4463_ = lean_ctor_get(v_toGoalState_4456_, 2);
v_parents_4464_ = lean_ctor_get(v_toGoalState_4456_, 3);
v_congrTable_4465_ = lean_ctor_get(v_toGoalState_4456_, 4);
v_appMap_4466_ = lean_ctor_get(v_toGoalState_4456_, 5);
v_indicesFound_4467_ = lean_ctor_get(v_toGoalState_4456_, 6);
v_internalizing_4468_ = lean_ctor_get(v_toGoalState_4456_, 8);
v_inconsistent_4469_ = lean_ctor_get_uint8(v_toGoalState_4456_, sizeof(void*)*18);
v_nextIdx_4470_ = lean_ctor_get(v_toGoalState_4456_, 9);
v_newRawFacts_4471_ = lean_ctor_get(v_toGoalState_4456_, 10);
v_facts_4472_ = lean_ctor_get(v_toGoalState_4456_, 11);
v_extThms_4473_ = lean_ctor_get(v_toGoalState_4456_, 12);
v_ematch_4474_ = lean_ctor_get(v_toGoalState_4456_, 13);
v_inj_4475_ = lean_ctor_get(v_toGoalState_4456_, 14);
v_split_4476_ = lean_ctor_get(v_toGoalState_4456_, 15);
v_clean_4477_ = lean_ctor_get(v_toGoalState_4456_, 16);
v_sstates_4478_ = lean_ctor_get(v_toGoalState_4456_, 17);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_toGoalState_4456_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; 
v_unused_4493_ = lean_ctor_get(v_toGoalState_4456_, 7);
lean_dec(v_unused_4493_);
v___x_4480_ = v_toGoalState_4456_;
v_isShared_4481_ = v_isSharedCheck_4492_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_sstates_4478_);
lean_inc(v_clean_4477_);
lean_inc(v_split_4476_);
lean_inc(v_inj_4475_);
lean_inc(v_ematch_4474_);
lean_inc(v_extThms_4473_);
lean_inc(v_facts_4472_);
lean_inc(v_newRawFacts_4471_);
lean_inc(v_nextIdx_4470_);
lean_inc(v_internalizing_4468_);
lean_inc(v_indicesFound_4467_);
lean_inc(v_appMap_4466_);
lean_inc(v_congrTable_4465_);
lean_inc(v_parents_4464_);
lean_inc(v_exprs_4463_);
lean_inc(v_enodeMap_4462_);
lean_inc(v_nextDeclIdx_4461_);
lean_dec(v_toGoalState_4456_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4492_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4482_ = lean_box(0);
v___x_4483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 7, v___x_4483_);
v___x_4485_ = v___x_4480_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_nextDeclIdx_4461_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_enodeMap_4462_);
lean_ctor_set(v_reuseFailAlloc_4491_, 2, v_exprs_4463_);
lean_ctor_set(v_reuseFailAlloc_4491_, 3, v_parents_4464_);
lean_ctor_set(v_reuseFailAlloc_4491_, 4, v_congrTable_4465_);
lean_ctor_set(v_reuseFailAlloc_4491_, 5, v_appMap_4466_);
lean_ctor_set(v_reuseFailAlloc_4491_, 6, v_indicesFound_4467_);
lean_ctor_set(v_reuseFailAlloc_4491_, 7, v___x_4483_);
lean_ctor_set(v_reuseFailAlloc_4491_, 8, v_internalizing_4468_);
lean_ctor_set(v_reuseFailAlloc_4491_, 9, v_nextIdx_4470_);
lean_ctor_set(v_reuseFailAlloc_4491_, 10, v_newRawFacts_4471_);
lean_ctor_set(v_reuseFailAlloc_4491_, 11, v_facts_4472_);
lean_ctor_set(v_reuseFailAlloc_4491_, 12, v_extThms_4473_);
lean_ctor_set(v_reuseFailAlloc_4491_, 13, v_ematch_4474_);
lean_ctor_set(v_reuseFailAlloc_4491_, 14, v_inj_4475_);
lean_ctor_set(v_reuseFailAlloc_4491_, 15, v_split_4476_);
lean_ctor_set(v_reuseFailAlloc_4491_, 16, v_clean_4477_);
lean_ctor_set(v_reuseFailAlloc_4491_, 17, v_sstates_4478_);
lean_ctor_set_uint8(v_reuseFailAlloc_4491_, sizeof(void*)*18, v_inconsistent_4469_);
v___x_4485_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4487_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4485_);
v___x_4487_ = v___x_4459_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_mvarId_4457_);
v___x_4487_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_st_ref_put(v_a_4453_, v___x_4487_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4482_);
return v___x_4489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4495_);
lean_dec(v_a_4495_);
return v_res_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4498_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_a_4510_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4522_){
_start:
{
lean_object* v___x_4524_; lean_object* v_toGoalState_4525_; lean_object* v_toProcess_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4524_ = lean_st_ref_get(v_a_4522_);
v_toGoalState_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc_ref(v_toGoalState_4525_);
lean_dec(v___x_4524_);
v_toProcess_4526_ = lean_ctor_get(v_toGoalState_4525_, 7);
lean_inc_ref(v_toProcess_4526_);
lean_dec_ref(v_toGoalState_4525_);
v___x_4527_ = lean_array_get_size(v_toProcess_4526_);
v___x_4528_ = lean_unsigned_to_nat(1u);
v___x_4529_ = lean_nat_sub(v___x_4527_, v___x_4528_);
v___x_4530_ = lean_nat_dec_lt(v___x_4529_, v___x_4527_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_dec(v___x_4529_);
lean_dec_ref(v_toProcess_4526_);
v___x_4531_ = lean_box(0);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
return v___x_4532_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_toGoalState_4536_; lean_object* v_mvarId_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4573_; 
v___x_4533_ = lean_array_fget(v_toProcess_4526_, v___x_4529_);
lean_dec(v___x_4529_);
lean_dec_ref(v_toProcess_4526_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
v___x_4535_ = lean_st_ref_take(v_a_4522_);
v_toGoalState_4536_ = lean_ctor_get(v___x_4535_, 0);
v_mvarId_4537_ = lean_ctor_get(v___x_4535_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4539_ = v___x_4535_;
v_isShared_4540_ = v_isSharedCheck_4573_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_mvarId_4537_);
lean_inc(v_toGoalState_4536_);
lean_dec(v___x_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4573_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v_nextDeclIdx_4541_; lean_object* v_enodeMap_4542_; lean_object* v_exprs_4543_; lean_object* v_parents_4544_; lean_object* v_congrTable_4545_; lean_object* v_appMap_4546_; lean_object* v_indicesFound_4547_; lean_object* v_toProcess_4548_; lean_object* v_internalizing_4549_; uint8_t v_inconsistent_4550_; lean_object* v_nextIdx_4551_; lean_object* v_newRawFacts_4552_; lean_object* v_facts_4553_; lean_object* v_extThms_4554_; lean_object* v_ematch_4555_; lean_object* v_inj_4556_; lean_object* v_split_4557_; lean_object* v_clean_4558_; lean_object* v_sstates_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4572_; 
v_nextDeclIdx_4541_ = lean_ctor_get(v_toGoalState_4536_, 0);
v_enodeMap_4542_ = lean_ctor_get(v_toGoalState_4536_, 1);
v_exprs_4543_ = lean_ctor_get(v_toGoalState_4536_, 2);
v_parents_4544_ = lean_ctor_get(v_toGoalState_4536_, 3);
v_congrTable_4545_ = lean_ctor_get(v_toGoalState_4536_, 4);
v_appMap_4546_ = lean_ctor_get(v_toGoalState_4536_, 5);
v_indicesFound_4547_ = lean_ctor_get(v_toGoalState_4536_, 6);
v_toProcess_4548_ = lean_ctor_get(v_toGoalState_4536_, 7);
v_internalizing_4549_ = lean_ctor_get(v_toGoalState_4536_, 8);
v_inconsistent_4550_ = lean_ctor_get_uint8(v_toGoalState_4536_, sizeof(void*)*18);
v_nextIdx_4551_ = lean_ctor_get(v_toGoalState_4536_, 9);
v_newRawFacts_4552_ = lean_ctor_get(v_toGoalState_4536_, 10);
v_facts_4553_ = lean_ctor_get(v_toGoalState_4536_, 11);
v_extThms_4554_ = lean_ctor_get(v_toGoalState_4536_, 12);
v_ematch_4555_ = lean_ctor_get(v_toGoalState_4536_, 13);
v_inj_4556_ = lean_ctor_get(v_toGoalState_4536_, 14);
v_split_4557_ = lean_ctor_get(v_toGoalState_4536_, 15);
v_clean_4558_ = lean_ctor_get(v_toGoalState_4536_, 16);
v_sstates_4559_ = lean_ctor_get(v_toGoalState_4536_, 17);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_toGoalState_4536_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4561_ = v_toGoalState_4536_;
v_isShared_4562_ = v_isSharedCheck_4572_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_sstates_4559_);
lean_inc(v_clean_4558_);
lean_inc(v_split_4557_);
lean_inc(v_inj_4556_);
lean_inc(v_ematch_4555_);
lean_inc(v_extThms_4554_);
lean_inc(v_facts_4553_);
lean_inc(v_newRawFacts_4552_);
lean_inc(v_nextIdx_4551_);
lean_inc(v_internalizing_4549_);
lean_inc(v_toProcess_4548_);
lean_inc(v_indicesFound_4547_);
lean_inc(v_appMap_4546_);
lean_inc(v_congrTable_4545_);
lean_inc(v_parents_4544_);
lean_inc(v_exprs_4543_);
lean_inc(v_enodeMap_4542_);
lean_inc(v_nextDeclIdx_4541_);
lean_dec(v_toGoalState_4536_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4572_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4563_; lean_object* v___x_4565_; 
v___x_4563_ = lean_array_pop(v_toProcess_4548_);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 7, v___x_4563_);
v___x_4565_ = v___x_4561_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_nextDeclIdx_4541_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_enodeMap_4542_);
lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_exprs_4543_);
lean_ctor_set(v_reuseFailAlloc_4571_, 3, v_parents_4544_);
lean_ctor_set(v_reuseFailAlloc_4571_, 4, v_congrTable_4545_);
lean_ctor_set(v_reuseFailAlloc_4571_, 5, v_appMap_4546_);
lean_ctor_set(v_reuseFailAlloc_4571_, 6, v_indicesFound_4547_);
lean_ctor_set(v_reuseFailAlloc_4571_, 7, v___x_4563_);
lean_ctor_set(v_reuseFailAlloc_4571_, 8, v_internalizing_4549_);
lean_ctor_set(v_reuseFailAlloc_4571_, 9, v_nextIdx_4551_);
lean_ctor_set(v_reuseFailAlloc_4571_, 10, v_newRawFacts_4552_);
lean_ctor_set(v_reuseFailAlloc_4571_, 11, v_facts_4553_);
lean_ctor_set(v_reuseFailAlloc_4571_, 12, v_extThms_4554_);
lean_ctor_set(v_reuseFailAlloc_4571_, 13, v_ematch_4555_);
lean_ctor_set(v_reuseFailAlloc_4571_, 14, v_inj_4556_);
lean_ctor_set(v_reuseFailAlloc_4571_, 15, v_split_4557_);
lean_ctor_set(v_reuseFailAlloc_4571_, 16, v_clean_4558_);
lean_ctor_set(v_reuseFailAlloc_4571_, 17, v_sstates_4559_);
lean_ctor_set_uint8(v_reuseFailAlloc_4571_, sizeof(void*)*18, v_inconsistent_4550_);
v___x_4565_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
lean_object* v___x_4567_; 
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___x_4565_);
v___x_4567_ = v___x_4539_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v_mvarId_4537_);
v___x_4567_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_st_ref_put(v_a_4522_, v___x_4567_);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4534_);
return v___x_4569_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4574_);
lean_dec(v_a_4574_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; 
v___x_4588_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4577_);
return v___x_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec(v_a_4589_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4601_, lean_object* v_rhs_4602_, lean_object* v_proof_4603_, uint8_t v_isHEq_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4601_, v_rhs_4602_, v_proof_4603_, v_isHEq_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v___x_4617_; 
lean_dec_ref_known(v___x_4616_, 1);
lean_inc(v_a_4614_);
lean_inc_ref(v_a_4613_);
lean_inc(v_a_4612_);
lean_inc_ref(v_a_4611_);
lean_inc(v_a_4610_);
lean_inc_ref(v_a_4609_);
lean_inc(v_a_4608_);
lean_inc_ref(v_a_4607_);
lean_inc(v_a_4606_);
lean_inc(v_a_4605_);
v___x_4617_ = lean_grind_process_to_do(v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
return v___x_4617_;
}
else
{
return v___x_4616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4618_, lean_object* v_rhs_4619_, lean_object* v_proof_4620_, lean_object* v_isHEq_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
uint8_t v_isHEq_boxed_4633_; lean_object* v_res_4634_; 
v_isHEq_boxed_4633_ = lean_unbox(v_isHEq_4621_);
v_res_4634_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4618_, v_rhs_4619_, v_proof_4620_, v_isHEq_boxed_4633_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec(v_a_4622_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4635_, lean_object* v_rhs_4636_, lean_object* v_proof_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
uint8_t v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = 0;
v___x_4650_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4635_, v_rhs_4636_, v_proof_4637_, v___x_4649_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4651_, lean_object* v_rhs_4652_, lean_object* v_proof_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4651_, v_rhs_4652_, v_proof_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec(v_a_4654_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4666_, lean_object* v_rhs_4667_, lean_object* v_proof_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
uint8_t v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = 1;
v___x_4681_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4666_, v_rhs_4667_, v_proof_4668_, v___x_4680_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4682_, lean_object* v_rhs_4683_, lean_object* v_proof_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4682_, v_rhs_4683_, v_proof_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec(v_a_4685_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v_toGoalState_4701_; lean_object* v_mvarId_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4739_; 
v___x_4700_ = lean_st_ref_take(v_a_4698_);
v_toGoalState_4701_ = lean_ctor_get(v___x_4700_, 0);
v_mvarId_4702_ = lean_ctor_get(v___x_4700_, 1);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4704_ = v___x_4700_;
v_isShared_4705_ = v_isSharedCheck_4739_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_mvarId_4702_);
lean_inc(v_toGoalState_4701_);
lean_dec(v___x_4700_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4739_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v_nextDeclIdx_4706_; lean_object* v_enodeMap_4707_; lean_object* v_exprs_4708_; lean_object* v_parents_4709_; lean_object* v_congrTable_4710_; lean_object* v_appMap_4711_; lean_object* v_indicesFound_4712_; lean_object* v_toProcess_4713_; lean_object* v_internalizing_4714_; uint8_t v_inconsistent_4715_; lean_object* v_nextIdx_4716_; lean_object* v_newRawFacts_4717_; lean_object* v_facts_4718_; lean_object* v_extThms_4719_; lean_object* v_ematch_4720_; lean_object* v_inj_4721_; lean_object* v_split_4722_; lean_object* v_clean_4723_; lean_object* v_sstates_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4738_; 
v_nextDeclIdx_4706_ = lean_ctor_get(v_toGoalState_4701_, 0);
v_enodeMap_4707_ = lean_ctor_get(v_toGoalState_4701_, 1);
v_exprs_4708_ = lean_ctor_get(v_toGoalState_4701_, 2);
v_parents_4709_ = lean_ctor_get(v_toGoalState_4701_, 3);
v_congrTable_4710_ = lean_ctor_get(v_toGoalState_4701_, 4);
v_appMap_4711_ = lean_ctor_get(v_toGoalState_4701_, 5);
v_indicesFound_4712_ = lean_ctor_get(v_toGoalState_4701_, 6);
v_toProcess_4713_ = lean_ctor_get(v_toGoalState_4701_, 7);
v_internalizing_4714_ = lean_ctor_get(v_toGoalState_4701_, 8);
v_inconsistent_4715_ = lean_ctor_get_uint8(v_toGoalState_4701_, sizeof(void*)*18);
v_nextIdx_4716_ = lean_ctor_get(v_toGoalState_4701_, 9);
v_newRawFacts_4717_ = lean_ctor_get(v_toGoalState_4701_, 10);
v_facts_4718_ = lean_ctor_get(v_toGoalState_4701_, 11);
v_extThms_4719_ = lean_ctor_get(v_toGoalState_4701_, 12);
v_ematch_4720_ = lean_ctor_get(v_toGoalState_4701_, 13);
v_inj_4721_ = lean_ctor_get(v_toGoalState_4701_, 14);
v_split_4722_ = lean_ctor_get(v_toGoalState_4701_, 15);
v_clean_4723_ = lean_ctor_get(v_toGoalState_4701_, 16);
v_sstates_4724_ = lean_ctor_get(v_toGoalState_4701_, 17);
v_isSharedCheck_4738_ = !lean_is_exclusive(v_toGoalState_4701_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4726_ = v_toGoalState_4701_;
v_isShared_4727_ = v_isSharedCheck_4738_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_sstates_4724_);
lean_inc(v_clean_4723_);
lean_inc(v_split_4722_);
lean_inc(v_inj_4721_);
lean_inc(v_ematch_4720_);
lean_inc(v_extThms_4719_);
lean_inc(v_facts_4718_);
lean_inc(v_newRawFacts_4717_);
lean_inc(v_nextIdx_4716_);
lean_inc(v_internalizing_4714_);
lean_inc(v_toProcess_4713_);
lean_inc(v_indicesFound_4712_);
lean_inc(v_appMap_4711_);
lean_inc(v_congrTable_4710_);
lean_inc(v_parents_4709_);
lean_inc(v_exprs_4708_);
lean_inc(v_enodeMap_4707_);
lean_inc(v_nextDeclIdx_4706_);
lean_dec(v_toGoalState_4701_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4738_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4731_; 
v___x_4728_ = lean_box(0);
v___x_4729_ = l_Lean_PersistentArray_push___redArg(v_facts_4718_, v_fact_4697_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 11, v___x_4729_);
v___x_4731_ = v___x_4726_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_nextDeclIdx_4706_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_enodeMap_4707_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_exprs_4708_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_parents_4709_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_congrTable_4710_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v_appMap_4711_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_indicesFound_4712_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_toProcess_4713_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_internalizing_4714_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_nextIdx_4716_);
lean_ctor_set(v_reuseFailAlloc_4737_, 10, v_newRawFacts_4717_);
lean_ctor_set(v_reuseFailAlloc_4737_, 11, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4737_, 12, v_extThms_4719_);
lean_ctor_set(v_reuseFailAlloc_4737_, 13, v_ematch_4720_);
lean_ctor_set(v_reuseFailAlloc_4737_, 14, v_inj_4721_);
lean_ctor_set(v_reuseFailAlloc_4737_, 15, v_split_4722_);
lean_ctor_set(v_reuseFailAlloc_4737_, 16, v_clean_4723_);
lean_ctor_set(v_reuseFailAlloc_4737_, 17, v_sstates_4724_);
lean_ctor_set_uint8(v_reuseFailAlloc_4737_, sizeof(void*)*18, v_inconsistent_4715_);
v___x_4731_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4733_; 
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4731_);
v___x_4733_ = v___x_4704_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_mvarId_4702_);
v___x_4733_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4734_ = lean_st_ref_put(v_a_4698_, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4728_);
return v___x_4735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4740_, v_a_4741_);
lean_dec(v_a_4741_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4744_, v_a_4745_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec(v_a_4758_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4770_, lean_object* v_rhs_4771_, lean_object* v_proof_4772_, lean_object* v_generation_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v___x_4785_; 
lean_inc_ref(v_rhs_4771_);
lean_inc_ref(v_lhs_4770_);
v___x_4785_ = l_Lean_Meta_mkEq(v_lhs_4770_, v_rhs_4771_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4797_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc_n(v_a_4786_, 2);
lean_dec_ref_known(v___x_4785_, 1);
v___x_4787_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4786_, v_a_4774_);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; 
v_unused_4798_ = lean_ctor_get(v___x_4787_, 0);
lean_dec(v_unused_4798_);
v___x_4789_ = v___x_4787_;
v_isShared_4790_ = v_isSharedCheck_4797_;
goto v_resetjp_4788_;
}
else
{
lean_dec(v___x_4787_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4797_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
lean_ctor_set_tag(v___x_4789_, 1);
lean_ctor_set(v___x_4789_, 0, v_a_4786_);
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4786_);
v___x_4792_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
lean_object* v___x_4793_; 
lean_inc(v_a_4783_);
lean_inc_ref(v_a_4782_);
lean_inc(v_a_4781_);
lean_inc_ref(v_a_4780_);
lean_inc(v_a_4779_);
lean_inc_ref(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc(v_a_4774_);
lean_inc_ref(v___x_4792_);
lean_inc(v_generation_4773_);
lean_inc_ref(v_lhs_4770_);
v___x_4793_ = lean_grind_internalize(v_lhs_4770_, v_generation_4773_, v___x_4792_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v___x_4794_; 
lean_dec_ref_known(v___x_4793_, 1);
lean_inc(v_a_4783_);
lean_inc_ref(v_a_4782_);
lean_inc(v_a_4781_);
lean_inc_ref(v_a_4780_);
lean_inc(v_a_4779_);
lean_inc_ref(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc(v_a_4774_);
lean_inc_ref(v_rhs_4771_);
v___x_4794_ = lean_grind_internalize(v_rhs_4771_, v_generation_4773_, v___x_4792_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v___x_4795_; 
lean_dec_ref_known(v___x_4794_, 1);
v___x_4795_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4770_, v_rhs_4771_, v_proof_4772_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
return v___x_4795_;
}
else
{
lean_dec_ref(v_proof_4772_);
lean_dec_ref(v_rhs_4771_);
lean_dec_ref(v_lhs_4770_);
return v___x_4794_;
}
}
else
{
lean_dec_ref(v___x_4792_);
lean_dec(v_generation_4773_);
lean_dec_ref(v_proof_4772_);
lean_dec_ref(v_rhs_4771_);
lean_dec_ref(v_lhs_4770_);
return v___x_4793_;
}
}
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec(v_generation_4773_);
lean_dec_ref(v_proof_4772_);
lean_dec_ref(v_rhs_4771_);
lean_dec_ref(v_lhs_4770_);
v_a_4799_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4785_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4785_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4807_, lean_object* v_rhs_4808_, lean_object* v_proof_4809_, lean_object* v_generation_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4807_, v_rhs_4808_, v_proof_4809_, v_generation_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec(v_a_4811_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4823_, lean_object* v_generation_4824_, lean_object* v_p_4825_, uint8_t v_isNeg_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_box(0);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc_ref(v_a_4831_);
lean_inc(v_a_4830_);
lean_inc_ref(v_a_4829_);
lean_inc(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_p_4825_);
v___x_4839_ = lean_grind_internalize(v_p_4825_, v_generation_4824_, v___x_4838_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_dec_ref_known(v___x_4839_, 1);
if (v_isNeg_4826_ == 0)
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4831_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4842_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v___x_4840_, 1);
v___x_4842_ = l_Lean_Meta_mkEqTrue(v_proof_4823_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4844_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
v___x_4844_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4825_, v_a_4841_, v_a_4843_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
return v___x_4844_;
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
lean_dec(v_a_4841_);
lean_dec_ref(v_p_4825_);
v_a_4845_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4842_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4842_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec_ref(v_p_4825_);
lean_dec_ref(v_proof_4823_);
v_a_4853_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4840_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4840_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4831_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = l_Lean_Meta_mkEqFalse(v_proof_4823_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4825_, v_a_4862_, v_a_4864_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
return v___x_4865_;
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
lean_dec(v_a_4862_);
lean_dec_ref(v_p_4825_);
v_a_4866_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4863_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4863_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec_ref(v_p_4825_);
lean_dec_ref(v_proof_4823_);
v_a_4874_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4861_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4861_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4825_);
lean_dec_ref(v_proof_4823_);
return v___x_4839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4882_, lean_object* v_generation_4883_, lean_object* v_p_4884_, lean_object* v_isNeg_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
uint8_t v_isNeg_boxed_4897_; lean_object* v_res_4898_; 
v_isNeg_boxed_4897_ = lean_unbox(v_isNeg_4885_);
v_res_4898_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4882_, v_generation_4883_, v_p_4884_, v_isNeg_boxed_4897_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
lean_dec(v_a_4887_);
lean_dec(v_a_4886_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4899_, lean_object* v_generation_4900_, lean_object* v_p_4901_, lean_object* v_lhs_4902_, lean_object* v_rhs_4903_, uint8_t v_isNeg_4904_, uint8_t v_isHEq_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
if (v_isNeg_4904_ == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_inc_ref(v_p_4901_);
v___x_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4917_, 0, v_p_4901_);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc(v_a_4906_);
lean_inc_ref(v___x_4917_);
lean_inc(v_generation_4900_);
lean_inc_ref(v_lhs_4902_);
v___x_4918_ = lean_grind_internalize(v_lhs_4902_, v_generation_4900_, v___x_4917_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref_known(v___x_4918_, 1);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc(v_a_4906_);
lean_inc_ref(v_rhs_4903_);
v___x_4919_ = lean_grind_internalize(v_rhs_4903_, v_generation_4900_, v___x_4917_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_dec_ref_known(v___x_4919_, 1);
v___x_4920_ = lean_box(0);
v___x_4921_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4901_, v___x_4920_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v___x_4922_; 
lean_dec_ref_known(v___x_4921_, 1);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4902_, v_rhs_4903_, v_proof_4899_, v_isHEq_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
return v___x_4922_;
}
else
{
lean_dec_ref(v_rhs_4903_);
lean_dec_ref(v_lhs_4902_);
lean_dec_ref(v_proof_4899_);
return v___x_4921_;
}
}
else
{
lean_dec_ref(v_rhs_4903_);
lean_dec_ref(v_lhs_4902_);
lean_dec_ref(v_p_4901_);
lean_dec_ref(v_proof_4899_);
return v___x_4919_;
}
}
else
{
lean_dec_ref_known(v___x_4917_, 1);
lean_dec_ref(v_rhs_4903_);
lean_dec_ref(v_lhs_4902_);
lean_dec_ref(v_p_4901_);
lean_dec(v_generation_4900_);
lean_dec_ref(v_proof_4899_);
return v___x_4918_;
}
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; 
lean_dec_ref(v_rhs_4903_);
lean_dec_ref(v_lhs_4902_);
v___x_4923_ = lean_box(0);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc(v_a_4906_);
lean_inc_ref(v_p_4901_);
v___x_4924_ = lean_grind_internalize(v_p_4901_, v_generation_4900_, v___x_4923_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_object* v___x_4925_; 
lean_dec_ref_known(v___x_4924_, 1);
v___x_4925_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4910_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4927_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4926_);
lean_dec_ref_known(v___x_4925_, 1);
v___x_4927_ = l_Lean_Meta_mkEqFalse(v_proof_4899_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4929_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___x_4927_, 1);
v___x_4929_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4901_, v_a_4926_, v_a_4928_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
return v___x_4929_;
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec(v_a_4926_);
lean_dec_ref(v_p_4901_);
v_a_4930_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4927_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4927_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec_ref(v_p_4901_);
lean_dec_ref(v_proof_4899_);
v_a_4938_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4925_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4925_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
else
{
lean_dec_ref(v_p_4901_);
lean_dec_ref(v_proof_4899_);
return v___x_4924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4946_ = _args[0];
lean_object* v_generation_4947_ = _args[1];
lean_object* v_p_4948_ = _args[2];
lean_object* v_lhs_4949_ = _args[3];
lean_object* v_rhs_4950_ = _args[4];
lean_object* v_isNeg_4951_ = _args[5];
lean_object* v_isHEq_4952_ = _args[6];
lean_object* v_a_4953_ = _args[7];
lean_object* v_a_4954_ = _args[8];
lean_object* v_a_4955_ = _args[9];
lean_object* v_a_4956_ = _args[10];
lean_object* v_a_4957_ = _args[11];
lean_object* v_a_4958_ = _args[12];
lean_object* v_a_4959_ = _args[13];
lean_object* v_a_4960_ = _args[14];
lean_object* v_a_4961_ = _args[15];
lean_object* v_a_4962_ = _args[16];
lean_object* v_a_4963_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4964_; uint8_t v_isHEq_boxed_4965_; lean_object* v_res_4966_; 
v_isNeg_boxed_4964_ = lean_unbox(v_isNeg_4951_);
v_isHEq_boxed_4965_ = lean_unbox(v_isHEq_4952_);
v_res_4966_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4946_, v_generation_4947_, v_p_4948_, v_lhs_4949_, v_rhs_4950_, v_isNeg_boxed_4964_, v_isHEq_boxed_4965_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec(v_a_4953_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4970_, lean_object* v_generation_4971_, lean_object* v_p_4972_, uint8_t v_isNeg_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4985_; 
lean_inc_ref(v_p_4972_);
v___x_4985_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4972_, v_a_4981_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_4987_ = l_Lean_Expr_cleanupAnnotations(v_a_4986_);
v___x_4988_ = l_Lean_Expr_isApp(v___x_4987_);
if (v___x_4988_ == 0)
{
lean_object* v___x_4989_; 
lean_dec_ref(v___x_4987_);
v___x_4989_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_4989_;
}
else
{
lean_object* v_arg_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v_arg_4990_ = lean_ctor_get(v___x_4987_, 1);
lean_inc_ref(v_arg_4990_);
v___x_4991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4987_);
v___x_4992_ = l_Lean_Expr_isApp(v___x_4991_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; 
lean_dec_ref(v___x_4991_);
lean_dec_ref(v_arg_4990_);
v___x_4993_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_4993_;
}
else
{
lean_object* v_arg_4994_; lean_object* v___x_4995_; uint8_t v___x_4996_; 
v_arg_4994_ = lean_ctor_get(v___x_4991_, 1);
lean_inc_ref(v_arg_4994_);
v___x_4995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4991_);
v___x_4996_ = l_Lean_Expr_isApp(v___x_4995_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
lean_dec_ref(v___x_4995_);
lean_dec_ref(v_arg_4994_);
lean_dec_ref(v_arg_4990_);
v___x_4997_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_4997_;
}
else
{
lean_object* v_arg_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
v_arg_4998_ = lean_ctor_get(v___x_4995_, 1);
lean_inc_ref(v_arg_4998_);
v___x_4999_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4995_);
v___x_5000_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5001_ = l_Lean_Expr_isConstOf(v___x_4999_, v___x_5000_);
if (v___x_5001_ == 0)
{
uint8_t v___x_5002_; 
lean_dec_ref(v_arg_4994_);
v___x_5002_ = l_Lean_Expr_isApp(v___x_4999_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_dec_ref(v___x_4999_);
lean_dec_ref(v_arg_4998_);
lean_dec_ref(v_arg_4990_);
v___x_5003_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_5003_;
}
else
{
lean_object* v___x_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; 
v___x_5004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4999_);
v___x_5005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5006_ = l_Lean_Expr_isConstOf(v___x_5004_, v___x_5005_);
lean_dec_ref(v___x_5004_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; 
lean_dec_ref(v_arg_4998_);
lean_dec_ref(v_arg_4990_);
v___x_5007_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_5007_;
}
else
{
lean_object* v___x_5008_; 
v___x_5008_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4970_, v_generation_4971_, v_p_4972_, v_arg_4998_, v_arg_4990_, v_isNeg_4973_, v___x_5006_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_5008_;
}
}
}
else
{
uint8_t v___x_5009_; 
lean_dec_ref(v___x_4999_);
v___x_5009_ = l_Lean_Expr_isProp(v_arg_4998_);
lean_dec_ref(v_arg_4998_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
v___x_5010_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4970_, v_generation_4971_, v_p_4972_, v_arg_4994_, v_arg_4990_, v_isNeg_4973_, v___x_5009_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; 
lean_dec_ref(v_arg_4994_);
lean_dec_ref(v_arg_4990_);
v___x_5011_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4970_, v_generation_4971_, v_p_4972_, v_isNeg_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_5011_;
}
}
}
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec_ref(v_p_4972_);
lean_dec(v_generation_4971_);
lean_dec_ref(v_proof_4970_);
v_a_5012_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4985_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4985_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5020_, lean_object* v_generation_5021_, lean_object* v_p_5022_, lean_object* v_isNeg_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
uint8_t v_isNeg_boxed_5035_; lean_object* v_res_5036_; 
v_isNeg_boxed_5035_ = lean_unbox(v_isNeg_5023_);
v_res_5036_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5020_, v_generation_5021_, v_p_5022_, v_isNeg_boxed_5035_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
lean_dec(v_a_5029_);
lean_dec_ref(v_a_5028_);
lean_dec(v_a_5027_);
lean_dec_ref(v_a_5026_);
lean_dec(v_a_5025_);
lean_dec(v_a_5024_);
return v_res_5036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5045_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5046_ = l_Lean_Name_append(v___x_5045_, v___x_5044_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5047_, lean_object* v_proof_5048_, lean_object* v_generation_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___x_5092_; lean_object* v_toCold_5093_; lean_object* v_options_5094_; uint8_t v_hasTrace_5095_; 
lean_inc_ref(v_fact_5047_);
v___x_5092_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5047_, v_a_5050_);
lean_dec_ref(v___x_5092_);
v_toCold_5093_ = lean_ctor_get(v_a_5058_, 0);
v_options_5094_ = lean_ctor_get(v_toCold_5093_, 2);
v_hasTrace_5095_ = lean_ctor_get_uint8(v_options_5094_, sizeof(void*)*1);
if (v_hasTrace_5095_ == 0)
{
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
goto v___jp_5074_;
}
else
{
lean_object* v_inheritedTraceOptions_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; 
v_inheritedTraceOptions_5096_ = lean_ctor_get(v_toCold_5093_, 11);
v___x_5097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5099_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5096_, v_options_5094_, v___x_5098_);
if (v___x_5099_ == 0)
{
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
goto v___jp_5074_;
}
else
{
lean_object* v___x_5100_; 
v___x_5100_ = l_Lean_Meta_Grind_updateLastTag(v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec_ref_known(v___x_5100_, 1);
lean_inc_ref(v_fact_5047_);
v___x_5101_ = l_Lean_MessageData_ofExpr(v_fact_5047_);
v___x_5102_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5097_, v___x_5101_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_dec_ref_known(v___x_5102_, 1);
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
goto v___jp_5074_;
}
else
{
lean_dec(v_generation_5049_);
lean_dec_ref(v_proof_5048_);
lean_dec_ref(v_fact_5047_);
return v___x_5102_;
}
}
else
{
lean_dec(v_generation_5049_);
lean_dec_ref(v_proof_5048_);
lean_dec_ref(v_fact_5047_);
return v___x_5100_;
}
}
}
v___jp_5061_:
{
uint8_t v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = 0;
v___x_5073_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5048_, v_generation_5049_, v_fact_5047_, v___x_5072_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_);
return v___x_5073_;
}
v___jp_5074_:
{
lean_object* v___x_5085_; uint8_t v___x_5086_; 
lean_inc_ref(v_fact_5047_);
v___x_5085_ = l_Lean_Expr_cleanupAnnotations(v_fact_5047_);
v___x_5086_ = l_Lean_Expr_isApp(v___x_5085_);
if (v___x_5086_ == 0)
{
lean_dec_ref(v___x_5085_);
v___y_5062_ = v___y_5075_;
v___y_5063_ = v___y_5076_;
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
goto v___jp_5061_;
}
else
{
lean_object* v_arg_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; 
v_arg_5087_ = lean_ctor_get(v___x_5085_, 1);
lean_inc_ref(v_arg_5087_);
v___x_5088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5085_);
v___x_5089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5090_ = l_Lean_Expr_isConstOf(v___x_5088_, v___x_5089_);
lean_dec_ref(v___x_5088_);
if (v___x_5090_ == 0)
{
lean_dec_ref(v_arg_5087_);
v___y_5062_ = v___y_5075_;
v___y_5063_ = v___y_5076_;
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
goto v___jp_5061_;
}
else
{
lean_object* v___x_5091_; 
lean_dec_ref(v_fact_5047_);
v___x_5091_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5048_, v_generation_5049_, v_arg_5087_, v___x_5090_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
return v___x_5091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5103_, lean_object* v_proof_5104_, lean_object* v_generation_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5103_, v_proof_5104_, v_generation_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec(v_a_5107_);
lean_dec(v_a_5106_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5121_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; uint8_t v___x_5134_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5134_ = lean_unbox(v_a_5133_);
lean_dec(v_a_5133_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5135_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5136_ = l_Lean_Core_checkSystem(v___x_5135_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v___x_5137_; 
lean_dec_ref_known(v___x_5136_, 1);
v___x_5137_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5121_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5211_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5211_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5211_ == 0)
{
v___x_5140_ = v___x_5137_;
v_isShared_5141_ = v_isSharedCheck_5211_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5137_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5211_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
if (lean_obj_tag(v_a_5138_) == 1)
{
lean_object* v_val_5142_; 
lean_del_object(v___x_5140_);
v_val_5142_ = lean_ctor_get(v_a_5138_, 0);
lean_inc(v_val_5142_);
lean_dec_ref_known(v_a_5138_, 1);
switch(lean_obj_tag(v_val_5142_))
{
case 0:
{
lean_object* v_lhs_5143_; lean_object* v_rhs_5144_; lean_object* v_proof_5145_; uint8_t v_isHEq_5146_; lean_object* v___x_5147_; 
v_lhs_5143_ = lean_ctor_get(v_val_5142_, 0);
lean_inc_ref(v_lhs_5143_);
v_rhs_5144_ = lean_ctor_get(v_val_5142_, 1);
lean_inc_ref(v_rhs_5144_);
v_proof_5145_ = lean_ctor_get(v_val_5142_, 2);
lean_inc_ref(v_proof_5145_);
v_isHEq_5146_ = lean_ctor_get_uint8(v_val_5142_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5142_, 3);
v___x_5147_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5143_, v_rhs_5144_, v_proof_5145_, v_isHEq_5146_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_dec_ref_known(v___x_5147_, 1);
goto _start;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5147_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5147_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
case 1:
{
lean_object* v_prop_5157_; lean_object* v_proof_5158_; lean_object* v_generation_5159_; lean_object* v___x_5160_; 
v_prop_5157_ = lean_ctor_get(v_val_5142_, 0);
lean_inc_ref(v_prop_5157_);
v_proof_5158_ = lean_ctor_get(v_val_5142_, 1);
lean_inc_ref(v_proof_5158_);
v_generation_5159_ = lean_ctor_get(v_val_5142_, 2);
lean_inc(v_generation_5159_);
lean_dec_ref_known(v_val_5142_, 3);
v___x_5160_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5157_, v_proof_5158_, v_generation_5159_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_dec_ref_known(v___x_5160_, 1);
goto _start;
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
v_a_5162_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5160_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5160_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
case 2:
{
lean_object* v_e_5170_; lean_object* v___x_5171_; 
v_e_5170_ = lean_ctor_get(v_val_5142_, 0);
lean_inc_ref(v_e_5170_);
lean_dec_ref_known(v_val_5142_, 1);
v___x_5171_ = l_Lean_Meta_Grind_propagateUp(v_e_5170_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_dec_ref_known(v___x_5171_, 1);
goto _start;
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
v_a_5173_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5171_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5171_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
case 3:
{
lean_object* v_solverId_5181_; lean_object* v_lhs_5182_; lean_object* v_rhs_5183_; lean_object* v___x_5184_; 
v_solverId_5181_ = lean_ctor_get(v_val_5142_, 0);
lean_inc(v_solverId_5181_);
v_lhs_5182_ = lean_ctor_get(v_val_5142_, 1);
lean_inc_ref(v_lhs_5182_);
v_rhs_5183_ = lean_ctor_get(v_val_5142_, 2);
lean_inc_ref(v_rhs_5183_);
lean_dec_ref_known(v_val_5142_, 3);
v___x_5184_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5181_, v_lhs_5182_, v_rhs_5183_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v_solverId_5181_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_dec_ref_known(v___x_5184_, 1);
goto _start;
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
v_a_5186_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5184_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5184_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
default: 
{
lean_object* v_solverId_5194_; lean_object* v_lhs_5195_; lean_object* v_rhs_5196_; lean_object* v___x_5197_; 
v_solverId_5194_ = lean_ctor_get(v_val_5142_, 0);
lean_inc(v_solverId_5194_);
v_lhs_5195_ = lean_ctor_get(v_val_5142_, 1);
lean_inc_ref(v_lhs_5195_);
v_rhs_5196_ = lean_ctor_get(v_val_5142_, 2);
lean_inc_ref(v_rhs_5196_);
lean_dec_ref_known(v_val_5142_, 3);
v___x_5197_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5194_, v_lhs_5195_, v_rhs_5196_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v_solverId_5194_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_dec_ref_known(v___x_5197_, 1);
goto _start;
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
v_a_5199_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5197_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5197_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
}
}
else
{
lean_object* v___x_5207_; lean_object* v___x_5209_; 
lean_dec(v_a_5138_);
v___x_5207_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v___x_5207_);
v___x_5209_ = v___x_5140_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5207_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
}
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
v_a_5212_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5137_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5137_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
v_a_5220_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5136_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5136_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_object* v___x_5228_; 
v___x_5228_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5121_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5236_; 
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5236_ == 0)
{
lean_object* v_unused_5237_; 
v_unused_5237_ = lean_ctor_get(v___x_5228_, 0);
lean_dec(v_unused_5237_);
v___x_5230_ = v___x_5228_;
v_isShared_5231_ = v_isSharedCheck_5236_;
goto v_resetjp_5229_;
}
else
{
lean_dec(v___x_5228_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5236_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5232_; lean_object* v___x_5234_; 
v___x_5232_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v___x_5232_);
v___x_5234_ = v___x_5230_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v___x_5232_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
v_a_5238_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5228_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5228_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
v_a_5246_ = lean_ctor_get(v___x_5132_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5132_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5132_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5132_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec(v___y_5254_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5277_ = lean_box(0);
v___x_5278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec(v_a_5267_);
lean_dec(v_a_5266_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5291_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5281_ = v___x_5278_;
v_isShared_5282_ = v_isSharedCheck_5291_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5278_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5291_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v_fst_5283_; 
v_fst_5283_ = lean_ctor_get(v_a_5279_, 0);
lean_inc(v_fst_5283_);
lean_dec(v_a_5279_);
if (lean_obj_tag(v_fst_5283_) == 0)
{
lean_object* v___x_5285_; 
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v___x_5277_);
v___x_5285_ = v___x_5281_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5277_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
else
{
lean_object* v_val_5287_; lean_object* v___x_5289_; 
v_val_5287_ = lean_ctor_get(v_fst_5283_, 0);
lean_inc(v_val_5287_);
lean_dec_ref_known(v_fst_5283_, 1);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v_val_5287_);
v___x_5289_ = v___x_5281_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_val_5287_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
else
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5299_; 
v_a_5292_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5294_ = v___x_5278_;
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5278_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5297_; 
if (v_isShared_5295_ == 0)
{
v___x_5297_ = v___x_5294_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = lean_grind_process_to_do(v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5312_, lean_object* v_a_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v___x_5325_; 
v___x_5325_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5326_, lean_object* v_a_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5326_, v_a_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v_a_5327_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5340_, lean_object* v_proof_5341_, lean_object* v_generation_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
uint8_t v___x_5354_; 
lean_inc_ref(v_fact_5340_);
v___x_5354_ = l_Lean_Expr_isTrue(v_fact_5340_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; 
v___x_5355_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5343_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5386_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5358_ = v___x_5355_;
v_isShared_5359_ = v_isSharedCheck_5386_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5355_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5386_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
uint8_t v___x_5360_; 
v___x_5360_ = lean_unbox(v_a_5356_);
lean_dec(v_a_5356_);
if (v___x_5360_ == 0)
{
lean_object* v___x_5361_; 
lean_del_object(v___x_5358_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
lean_inc(v_a_5350_);
lean_inc_ref(v_a_5349_);
lean_inc(v_a_5348_);
lean_inc_ref(v_a_5347_);
lean_inc(v_a_5346_);
lean_inc_ref(v_a_5345_);
lean_inc(v_a_5344_);
lean_inc(v_a_5343_);
v___x_5361_ = lean_grind_process_to_do(v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v___x_5362_; 
lean_dec_ref_known(v___x_5361_, 1);
v___x_5362_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5343_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5373_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5365_ = v___x_5362_;
v_isShared_5366_ = v_isSharedCheck_5373_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5362_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5373_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
uint8_t v___x_5367_; 
v___x_5367_ = lean_unbox(v_a_5363_);
lean_dec(v_a_5363_);
if (v___x_5367_ == 0)
{
lean_object* v___x_5368_; 
lean_del_object(v___x_5365_);
v___x_5368_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5340_, v_proof_5341_, v_generation_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_);
return v___x_5368_;
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
v___x_5369_ = lean_box(0);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v___x_5369_);
v___x_5371_ = v___x_5365_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
v_a_5374_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5362_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5362_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
else
{
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
return v___x_5361_;
}
}
else
{
lean_object* v___x_5382_; lean_object* v___x_5384_; 
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
v___x_5382_ = lean_box(0);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5382_);
v___x_5384_ = v___x_5358_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5382_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
v_a_5387_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5355_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5355_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
lean_dec(v_generation_5342_);
lean_dec_ref(v_proof_5341_);
lean_dec_ref(v_fact_5340_);
v___x_5395_ = lean_box(0);
v___x_5396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5395_);
return v___x_5396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5397_, lean_object* v_proof_5398_, lean_object* v_generation_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Meta_Grind_add(v_fact_5397_, v_proof_5398_, v_generation_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
lean_dec(v_a_5405_);
lean_dec_ref(v_a_5404_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec(v_a_5400_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5412_, lean_object* v_generation_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v___x_5425_; 
lean_inc(v_fvarId_5412_);
v___x_5425_ = l_Lean_FVarId_getType___redArg(v_fvarId_5412_, v_a_5420_, v_a_5422_, v_a_5423_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc(v_a_5426_);
lean_dec_ref_known(v___x_5425_, 1);
v___x_5427_ = l_Lean_mkFVar(v_fvarId_5412_);
v___x_5428_ = l_Lean_Meta_Grind_add(v_a_5426_, v___x_5427_, v_generation_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
return v___x_5428_;
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec(v_generation_5413_);
lean_dec(v_fvarId_5412_);
v_a_5429_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5425_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5425_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5437_, lean_object* v_generation_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5437_, v_generation_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
lean_dec(v_a_5448_);
lean_dec_ref(v_a_5447_);
lean_dec(v_a_5446_);
lean_dec_ref(v_a_5445_);
lean_dec(v_a_5444_);
lean_dec_ref(v_a_5443_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
lean_dec(v_a_5440_);
lean_dec(v_a_5439_);
return v_res_5450_;
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
