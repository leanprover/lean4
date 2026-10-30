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
lean_object* l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_23086__boxed_357_; lean_object* v_res_358_; 
v_x_23086__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_23086__boxed_357_, v_x_356_);
lean_dec_ref(v___x_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint64_t v___x_362_; size_t v_h_363_; lean_object* v___x_364_; 
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
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v___x_446_; 
v_head_399_ = lean_ctor_get(v_as_x27_385_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_385_, 1);
v___x_401_ = lean_box(0);
v___x_446_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_399_);
if (v___x_446_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v___x_448_; 
lean_inc(v_head_399_);
v___x_448_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_399_, v___y_387_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; uint8_t v___x_450_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = lean_unbox(v_a_449_);
lean_dec(v_a_449_);
if (v___x_450_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_toCold_452_; lean_object* v_options_453_; uint8_t v_hasTrace_454_; 
v_toCold_452_ = lean_ctor_get(v___y_395_, 0);
v_options_453_ = lean_ctor_get(v_toCold_452_, 2);
v_hasTrace_454_ = lean_ctor_get_uint8(v_options_453_, sizeof(void*)*1);
if (v_hasTrace_454_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_inheritedTraceOptions_455_ = lean_ctor_get(v_toCold_452_, 11);
v___x_456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_457_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_458_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_455_, v_options_453_, v___x_457_);
if (v___x_458_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_updateLastTag(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref_known(v___x_459_, 1);
v___x_460_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_461_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_456_, v___x_462_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_dec_ref_known(v___x_463_, 1);
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
return v___x_463_;
}
}
else
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_a_464_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_448_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_448_);
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
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toGoalState_405_; lean_object* v_mvarId_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_445_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toGoalState_405_ = lean_ctor_get(v___x_404_, 0);
v_mvarId_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_445_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_445_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_mvarId_406_);
lean_inc(v_toGoalState_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_445_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_nextDeclIdx_410_; lean_object* v_enodeMap_411_; lean_object* v_exprs_412_; lean_object* v_parents_413_; lean_object* v_congrTable_414_; lean_object* v_appMap_415_; lean_object* v_indicesFound_416_; lean_object* v_toProcess_417_; lean_object* v_internalizing_418_; uint8_t v_inconsistent_419_; lean_object* v_nextIdx_420_; lean_object* v_newRawFacts_421_; lean_object* v_facts_422_; lean_object* v_extThms_423_; lean_object* v_ematch_424_; lean_object* v_inj_425_; lean_object* v_split_426_; lean_object* v_clean_427_; lean_object* v_sstates_428_; lean_object* v_goalStack_429_; uint64_t v_introBase_430_; lean_object* v_numIntros_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_444_; 
v_nextDeclIdx_410_ = lean_ctor_get(v_toGoalState_405_, 0);
v_enodeMap_411_ = lean_ctor_get(v_toGoalState_405_, 1);
v_exprs_412_ = lean_ctor_get(v_toGoalState_405_, 2);
v_parents_413_ = lean_ctor_get(v_toGoalState_405_, 3);
v_congrTable_414_ = lean_ctor_get(v_toGoalState_405_, 4);
v_appMap_415_ = lean_ctor_get(v_toGoalState_405_, 5);
v_indicesFound_416_ = lean_ctor_get(v_toGoalState_405_, 6);
v_toProcess_417_ = lean_ctor_get(v_toGoalState_405_, 7);
v_internalizing_418_ = lean_ctor_get(v_toGoalState_405_, 8);
v_inconsistent_419_ = lean_ctor_get_uint8(v_toGoalState_405_, sizeof(void*)*20 + 8);
v_nextIdx_420_ = lean_ctor_get(v_toGoalState_405_, 9);
v_newRawFacts_421_ = lean_ctor_get(v_toGoalState_405_, 10);
v_facts_422_ = lean_ctor_get(v_toGoalState_405_, 11);
v_extThms_423_ = lean_ctor_get(v_toGoalState_405_, 12);
v_ematch_424_ = lean_ctor_get(v_toGoalState_405_, 13);
v_inj_425_ = lean_ctor_get(v_toGoalState_405_, 14);
v_split_426_ = lean_ctor_get(v_toGoalState_405_, 15);
v_clean_427_ = lean_ctor_get(v_toGoalState_405_, 16);
v_sstates_428_ = lean_ctor_get(v_toGoalState_405_, 17);
v_goalStack_429_ = lean_ctor_get(v_toGoalState_405_, 18);
v_introBase_430_ = lean_ctor_get_uint64(v_toGoalState_405_, sizeof(void*)*20);
v_numIntros_431_ = lean_ctor_get(v_toGoalState_405_, 19);
v_isSharedCheck_444_ = !lean_is_exclusive(v_toGoalState_405_);
if (v_isSharedCheck_444_ == 0)
{
v___x_433_ = v_toGoalState_405_;
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_numIntros_431_);
lean_inc(v_goalStack_429_);
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
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc(v_head_399_);
v___x_435_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_411_, v_congrTable_414_, v_head_399_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_nextDeclIdx_410_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_enodeMap_411_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_exprs_412_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_parents_413_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_appMap_415_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_indicesFound_416_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_toProcess_417_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_internalizing_418_);
lean_ctor_set(v_reuseFailAlloc_443_, 9, v_nextIdx_420_);
lean_ctor_set(v_reuseFailAlloc_443_, 10, v_newRawFacts_421_);
lean_ctor_set(v_reuseFailAlloc_443_, 11, v_facts_422_);
lean_ctor_set(v_reuseFailAlloc_443_, 12, v_extThms_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 13, v_ematch_424_);
lean_ctor_set(v_reuseFailAlloc_443_, 14, v_inj_425_);
lean_ctor_set(v_reuseFailAlloc_443_, 15, v_split_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 16, v_clean_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 17, v_sstates_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 18, v_goalStack_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 19, v_numIntros_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*20 + 8, v_inconsistent_419_);
lean_ctor_set_uint64(v_reuseFailAlloc_443_, sizeof(void*)*20, v_introBase_430_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_437_);
v___x_439_ = v___x_408_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_mvarId_406_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; 
v___x_440_ = lean_st_ref_put(v___y_403_, v___x_439_);
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
size_t v_x_23546__boxed_613_; lean_object* v_res_614_; 
v_x_23546__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_614_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_608_, v_00_u03b2_609_, v_x_610_, v_x_23546__boxed_613_, v_x_612_);
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
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_634_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___x_648_; 
v_head_632_ = lean_ctor_get(v_as_x27_618_, 0);
v_tail_633_ = lean_ctor_get(v_as_x27_618_, 1);
v___x_634_ = lean_box(0);
v___x_648_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_632_);
if (v___x_648_ == 0)
{
v_as_x27_618_ = v_tail_633_;
v_b_619_ = v___x_634_;
goto _start;
}
else
{
lean_object* v___x_650_; 
lean_inc(v_head_632_);
v___x_650_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_632_, v___y_620_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; uint8_t v___x_652_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_unbox(v_a_651_);
lean_dec(v_a_651_);
if (v___x_652_ == 0)
{
v_as_x27_618_ = v_tail_633_;
v_b_619_ = v___x_634_;
goto _start;
}
else
{
lean_object* v_toCold_654_; lean_object* v_options_655_; uint8_t v_hasTrace_656_; 
v_toCold_654_ = lean_ctor_get(v___y_628_, 0);
v_options_655_ = lean_ctor_get(v_toCold_654_, 2);
v_hasTrace_656_ = lean_ctor_get_uint8(v_options_655_, sizeof(void*)*1);
if (v_hasTrace_656_ == 0)
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
lean_object* v_inheritedTraceOptions_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_inheritedTraceOptions_657_ = lean_ctor_get(v_toCold_654_, 11);
v___x_658_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_659_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_657_, v_options_655_, v___x_659_);
if (v___x_660_ == 0)
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
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Grind_updateLastTag(v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec_ref_known(v___x_661_, 1);
v___x_662_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_632_);
v___x_663_ = l_Lean_MessageData_ofExpr(v_head_632_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_658_, v___x_664_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
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
return v___x_665_;
}
}
else
{
return v___x_661_;
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_650_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_650_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_674_, v_b_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec(v___y_676_);
lean_dec(v_as_x27_674_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_688_);
v___x_701_ = lean_box(0);
v___x_702_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_700_, v___x_701_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v___x_700_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_710_);
v___x_704_ = v___x_702_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_702_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_701_);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_701_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_parents_711_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_724_, lean_object* v_as_x27_725_, lean_object* v_b_726_, lean_object* v_a_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_725_, v_b_726_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_740_, lean_object* v_as_x27_741_, lean_object* v_b_742_, lean_object* v_a_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_740_, v_as_x27_741_, v_b_742_, v_a_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v_as_x27_741_);
lean_dec(v_as_740_);
return v_res_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_keys_756_);
v___x_760_ = lean_nat_dec_lt(v_i_757_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_i_757_);
return v___x_760_;
}
else
{
lean_object* v_k_x27_761_; uint8_t v___x_762_; 
v_k_x27_761_ = lean_array_fget_borrowed(v_keys_756_, v_i_757_);
v___x_762_ = l_Lean_instBEqMVarId_beq(v_k_758_, v_k_x27_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_i_757_, v___x_763_);
lean_dec(v_i_757_);
v_i_757_ = v___x_764_;
goto _start;
}
else
{
lean_dec(v_i_757_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_766_, lean_object* v_i_767_, lean_object* v_k_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_766_, v_i_767_, v_k_768_);
lean_dec(v_k_768_);
lean_dec_ref(v_keys_766_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_771_, size_t v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_es_774_; lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v_j_778_; lean_object* v___x_779_; 
v_es_774_ = lean_ctor_get(v_x_771_, 0);
v___x_775_ = lean_box(2);
v___x_776_ = ((size_t)31ULL);
v___x_777_ = lean_usize_land(v_x_772_, v___x_776_);
v_j_778_ = lean_usize_to_nat(v___x_777_);
v___x_779_ = lean_array_get_borrowed(v___x_775_, v_es_774_, v_j_778_);
lean_dec(v_j_778_);
switch(lean_obj_tag(v___x_779_))
{
case 0:
{
lean_object* v_key_780_; uint8_t v___x_781_; 
v_key_780_ = lean_ctor_get(v___x_779_, 0);
v___x_781_ = l_Lean_instBEqMVarId_beq(v_x_773_, v_key_780_);
return v___x_781_;
}
case 1:
{
lean_object* v_node_782_; size_t v___x_783_; size_t v___x_784_; 
v_node_782_ = lean_ctor_get(v___x_779_, 0);
v___x_783_ = ((size_t)5ULL);
v___x_784_ = lean_usize_shift_right(v_x_772_, v___x_783_);
v_x_771_ = v_node_782_;
v_x_772_ = v___x_784_;
goto _start;
}
default: 
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
}
}
else
{
lean_object* v_ks_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_ks_787_ = lean_ctor_get(v_x_771_, 0);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_787_, v___x_788_, v_x_773_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
size_t v_x_9681__boxed_793_; uint8_t v_res_794_; lean_object* v_r_795_; 
v_x_9681__boxed_793_ = lean_unbox_usize(v_x_791_);
lean_dec(v_x_791_);
v_res_794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_790_, v_x_9681__boxed_793_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_x_790_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
uint64_t v___x_798_; size_t v___x_799_; uint8_t v___x_800_; 
v___x_798_ = l_Lean_instHashableMVarId_hash(v_x_797_);
v___x_799_ = lean_uint64_to_usize(v___x_798_);
v___x_800_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_796_, v___x_799_, v_x_797_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_801_, v_x_802_);
lean_dec(v_x_802_);
lean_dec_ref(v_x_801_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; lean_object* v_mctx_809_; lean_object* v_eAssignment_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_808_ = lean_st_ref_get(v___y_806_);
v_mctx_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_mctx_809_);
lean_dec(v___x_808_);
v_eAssignment_810_ = lean_ctor_get(v_mctx_809_, 8);
lean_inc_ref(v_eAssignment_810_);
lean_dec_ref(v_mctx_809_);
v___x_811_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_810_, v_mvarId_805_);
lean_dec_ref(v_eAssignment_810_);
v___x_812_ = lean_box(v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec(v_mvarId_814_);
return v_res_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_828_ = l_Lean_mkConst(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_836_ = l_Lean_mkConst(v___x_835_, v___x_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_mvarId_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_904_; 
v___x_848_ = lean_st_ref_get(v_a_837_);
v_mvarId_849_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_mvarId_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_849_, v_a_844_);
lean_dec(v_mvarId_849_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_904_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_904_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_904_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; 
v___x_855_ = lean_unbox(v_a_851_);
lean_dec(v_a_851_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_del_object(v___x_853_);
v___x_856_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_841_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_857_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_841_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_841_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_866_ = l_Lean_mkApp4(v___x_864_, v_a_861_, v_a_863_, v_a_859_, v___x_865_);
v___x_867_ = l_Lean_Meta_Grind_closeGoal(v___x_866_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
return v___x_867_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_861_);
lean_dec(v_a_859_);
v_a_868_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_862_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_862_);
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
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_859_);
v_a_876_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_860_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_860_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v_a_884_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_858_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_858_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_856_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_856_);
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
else
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_900_);
v___x_902_ = v___x_853_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_917_, v___y_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v_mvarId_930_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_947_, v_x_948_, v_x_949_);
lean_dec(v_x_949_);
lean_dec_ref(v_x_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, size_t v_x_954_, lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
size_t v_x_9964__boxed_961_; uint8_t v_res_962_; lean_object* v_r_963_; 
v_x_9964__boxed_961_ = lean_unbox_usize(v_x_959_);
lean_dec(v_x_959_);
v_res_962_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_957_, v_x_958_, v_x_9964__boxed_961_, v_x_960_);
lean_dec(v_x_960_);
lean_dec_ref(v_x_958_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_heq_967_, lean_object* v_i_968_, lean_object* v_k_969_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_965_, v_i_968_, v_k_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_k_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_971_, v_keys_972_, v_vals_973_, v_heq_974_, v_i_975_, v_k_976_);
lean_dec(v_k_976_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_984_ = l_Lean_mkConst(v___x_983_, v___x_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_985_, lean_object* v_rhs_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; 
lean_inc_ref(v_rhs_986_);
lean_inc_ref(v_lhs_985_);
v___x_998_ = l_Lean_Meta_mkEq(v_lhs_985_, v_rhs_986_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
lean_inc(v_a_996_);
lean_inc_ref(v_a_995_);
lean_inc(v_a_994_);
lean_inc_ref(v_a_993_);
lean_inc(v_a_992_);
lean_inc_ref(v_a_991_);
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc(v_a_987_);
v___x_1000_ = lean_grind_mk_eq_proof(v_lhs_985_, v_rhs_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
lean_inc(v_a_999_);
v___x_1002_ = l_Lean_Meta_mkDecide(v_a_999_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1005_ = l_Lean_Expr_appArg_x21(v_a_1003_);
lean_dec(v_a_1003_);
v___x_1006_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_999_);
v___x_1007_ = l_Lean_mkApp3(v___x_1004_, v_a_999_, v___x_1005_, v___x_1006_);
v___x_1008_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_991_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1011_ = l_Lean_mkApp4(v___x_1010_, v_a_999_, v_a_1009_, v___x_1007_, v_a_1001_);
v___x_1012_ = l_Lean_Meta_Grind_closeGoal(v___x_1011_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v___x_1012_;
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v___x_1007_);
lean_dec(v_a_1001_);
lean_dec(v_a_999_);
v_a_1013_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1008_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1008_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_a_1001_);
lean_dec(v_a_999_);
v_a_1021_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1002_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1002_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
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
lean_dec(v_a_999_);
v_a_1029_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1000_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1000_);
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
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_rhs_986_);
lean_dec_ref(v_lhs_985_);
v_a_1037_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_998_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_998_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1045_, lean_object* v_rhs_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1045_, v_rhs_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1059_, lean_object* v_as_x27_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
if (lean_obj_tag(v_as_x27_1060_) == 0)
{
lean_object* v___x_1073_; 
lean_dec(v___x_1059_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_b_1061_);
return v___x_1073_;
}
else
{
lean_object* v_head_1074_; lean_object* v_tail_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_head_1074_ = lean_ctor_get(v_as_x27_1060_, 0);
v_tail_1075_ = lean_ctor_get(v_as_x27_1060_, 1);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_st_ref_get(v___y_1062_);
lean_inc(v_head_1074_);
v___x_1078_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1077_, v_head_1074_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v_self_1080_; lean_object* v_next_1081_; lean_object* v_root_1082_; lean_object* v_congr_1083_; lean_object* v_target_x3f_1084_; lean_object* v_proof_x3f_1085_; uint8_t v_flipped_1086_; lean_object* v_size_1087_; uint8_t v_interpreted_1088_; uint8_t v_ctor_1089_; uint8_t v_hasLambdas_1090_; uint8_t v_heqProofs_1091_; lean_object* v_idx_1092_; lean_object* v_generation_1093_; lean_object* v_mt_1094_; lean_object* v_sTerms_1095_; uint8_t v_funCC_1096_; lean_object* v_ematchDiagSource_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1109_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_self_1080_ = lean_ctor_get(v_a_1079_, 0);
v_next_1081_ = lean_ctor_get(v_a_1079_, 1);
v_root_1082_ = lean_ctor_get(v_a_1079_, 2);
v_congr_1083_ = lean_ctor_get(v_a_1079_, 3);
v_target_x3f_1084_ = lean_ctor_get(v_a_1079_, 4);
v_proof_x3f_1085_ = lean_ctor_get(v_a_1079_, 5);
v_flipped_1086_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12);
v_size_1087_ = lean_ctor_get(v_a_1079_, 6);
v_interpreted_1088_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12 + 1);
v_ctor_1089_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12 + 2);
v_hasLambdas_1090_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12 + 3);
v_heqProofs_1091_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12 + 4);
v_idx_1092_ = lean_ctor_get(v_a_1079_, 7);
v_generation_1093_ = lean_ctor_get(v_a_1079_, 8);
v_mt_1094_ = lean_ctor_get(v_a_1079_, 9);
v_sTerms_1095_ = lean_ctor_get(v_a_1079_, 10);
v_funCC_1096_ = lean_ctor_get_uint8(v_a_1079_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1097_ = lean_ctor_get(v_a_1079_, 11);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_a_1079_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1099_ = v_a_1079_;
v_isShared_1100_ = v_isSharedCheck_1109_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_ematchDiagSource_1097_);
lean_inc(v_sTerms_1095_);
lean_inc(v_mt_1094_);
lean_inc(v_generation_1093_);
lean_inc(v_idx_1092_);
lean_inc(v_size_1087_);
lean_inc(v_proof_x3f_1085_);
lean_inc(v_target_x3f_1084_);
lean_inc(v_congr_1083_);
lean_inc(v_root_1082_);
lean_inc(v_next_1081_);
lean_inc(v_self_1080_);
lean_dec(v_a_1079_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1109_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint8_t v___x_1101_; 
v___x_1101_ = lean_nat_dec_lt(v_mt_1094_, v___x_1059_);
lean_dec(v_mt_1094_);
if (v___x_1101_ == 0)
{
lean_del_object(v___x_1099_);
lean_dec(v_ematchDiagSource_1097_);
lean_dec(v_sTerms_1095_);
lean_dec(v_generation_1093_);
lean_dec(v_idx_1092_);
lean_dec(v_size_1087_);
lean_dec(v_proof_x3f_1085_);
lean_dec(v_target_x3f_1084_);
lean_dec_ref(v_congr_1083_);
lean_dec_ref(v_root_1082_);
lean_dec_ref(v_next_1081_);
lean_dec_ref(v_self_1080_);
v_as_x27_1060_ = v_tail_1075_;
v_b_1061_ = v___x_1076_;
goto _start;
}
else
{
lean_object* v___x_1104_; 
lean_inc(v___x_1059_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 9, v___x_1059_);
v___x_1104_ = v___x_1099_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_self_1080_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_next_1081_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_root_1082_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_congr_1083_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_target_x3f_1084_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_proof_x3f_1085_);
lean_ctor_set(v_reuseFailAlloc_1108_, 6, v_size_1087_);
lean_ctor_set(v_reuseFailAlloc_1108_, 7, v_idx_1092_);
lean_ctor_set(v_reuseFailAlloc_1108_, 8, v_generation_1093_);
lean_ctor_set(v_reuseFailAlloc_1108_, 9, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1108_, 10, v_sTerms_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 11, v_ematchDiagSource_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12, v_flipped_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12 + 1, v_interpreted_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12 + 2, v_ctor_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12 + 3, v_hasLambdas_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12 + 4, v_heqProofs_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1108_, sizeof(void*)*12 + 5, v_funCC_1096_);
v___x_1104_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
lean_inc(v_head_1074_);
v___x_1105_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1074_, v___x_1104_, v___y_1062_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; 
lean_dec_ref_known(v___x_1105_, 1);
v___x_1106_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1074_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_dec_ref_known(v___x_1106_, 1);
v_as_x27_1060_ = v_tail_1075_;
v_b_1061_ = v___x_1076_;
goto _start;
}
else
{
lean_dec(v___x_1059_);
return v___x_1106_;
}
}
else
{
lean_dec(v___x_1059_);
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v___x_1059_);
v_a_1110_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1078_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1078_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v_toGoalState_1131_; lean_object* v_ematch_1132_; lean_object* v_gmt_1133_; lean_object* v___x_1134_; 
v___x_1130_ = lean_st_ref_get(v_a_1119_);
v_toGoalState_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc_ref(v_toGoalState_1131_);
lean_dec(v___x_1130_);
v_ematch_1132_ = lean_ctor_get(v_toGoalState_1131_, 13);
lean_inc_ref(v_ematch_1132_);
lean_dec_ref(v_toGoalState_1131_);
v_gmt_1133_ = lean_ctor_get(v_ematch_1132_, 1);
lean_inc(v_gmt_1133_);
lean_dec_ref(v_ematch_1132_);
v___x_1134_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1118_, v_a_1119_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1135_);
lean_dec(v_a_1135_);
v___x_1137_ = lean_box(0);
v___x_1138_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1133_, v___x_1136_, v___x_1137_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v___x_1136_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1138_, 0);
lean_dec(v_unused_1146_);
v___x_1140_ = v___x_1138_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v___x_1138_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1137_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
return v___x_1138_;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_gmt_1133_);
v_a_1147_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1134_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1134_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_root_1155_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1168_, lean_object* v_as_x27_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1168_, v_as_x27_1169_, v_b_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec(v_as_x27_1169_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1183_, lean_object* v_as_1184_, lean_object* v_as_x27_1185_, lean_object* v_b_1186_, lean_object* v_a_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1183_, v_as_x27_1185_, v_b_1186_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1200_, lean_object* v_as_1201_, lean_object* v_as_x27_1202_, lean_object* v_b_1203_, lean_object* v_a_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1200_, v_as_1201_, v_as_x27_1202_, v_b_1203_, v_a_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
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
lean_dec(v_as_x27_1202_);
lean_dec(v_as_1201_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
if (lean_obj_tag(v_a_1217_) == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = l_List_reverse___redArg(v_a_1218_);
return v___x_1219_;
}
else
{
lean_object* v_head_1220_; lean_object* v_tail_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
v_head_1220_ = lean_ctor_get(v_a_1217_, 0);
v_tail_1221_ = lean_ctor_get(v_a_1217_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_a_1217_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1223_ = v_a_1217_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_tail_1221_);
lean_inc(v_head_1220_);
lean_dec(v_a_1217_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = l_Lean_MessageData_ofExpr(v_head_1220_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v_a_1218_);
lean_ctor_set(v___x_1223_, 0, v___x_1225_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_a_1218_);
v___x_1227_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v_a_1217_ = v_tail_1221_;
v_a_1218_ = v___x_1227_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1231_, lean_object* v_a_1232_, lean_object* v_fst_1233_, lean_object* v_a_1234_, lean_object* v_lams_1235_, lean_object* v_____r_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1231_, v_a_1234_, v___y_1237_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; uint8_t v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
if (v___x_1287_ == 0)
{
goto v___jp_1248_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc(v_fst_1233_);
v___x_1288_ = l_Array_reverse___redArg(v_fst_1233_);
lean_inc(v_snd_1231_);
v___x_1289_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1235_, v_snd_1231_, v___x_1288_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
goto v___jp_1248_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_fst_1233_);
lean_dec(v_snd_1231_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_fst_1233_);
lean_dec(v_snd_1231_);
v_a_1298_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1285_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1285_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
v___jp_1248_:
{
if (lean_obj_tag(v_snd_1231_) == 5)
{
lean_object* v_fn_1249_; lean_object* v_arg_1250_; lean_object* v___x_1251_; 
v_fn_1249_ = lean_ctor_get(v_snd_1231_, 0);
lean_inc_ref(v_fn_1249_);
v_arg_1250_ = lean_ctor_get(v_snd_1231_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1232_, v___y_1237_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_box(0);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc(v___y_1237_);
v___x_1254_ = lean_grind_internalize(v_snd_1231_, v_a_1252_, v___x_1253_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1264_; 
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1254_, 0);
lean_dec(v_unused_1265_);
v___x_1256_ = v___x_1254_;
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___x_1254_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1258_ = lean_array_push(v_fst_1233_, v_arg_1250_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_fn_1249_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1260_);
v___x_1262_ = v___x_1256_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_arg_1250_);
lean_dec_ref(v_fn_1249_);
lean_dec(v_fst_1233_);
v_a_1266_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1254_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v_arg_1250_);
lean_dec_ref_known(v_snd_1231_, 2);
lean_dec_ref(v_fn_1249_);
lean_dec(v_fst_1233_);
v_a_1274_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1251_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1251_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_fst_1233_);
lean_ctor_set(v___x_1282_, 1, v_snd_1231_);
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1306_ = _args[0];
lean_object* v_a_1307_ = _args[1];
lean_object* v_fst_1308_ = _args[2];
lean_object* v_a_1309_ = _args[3];
lean_object* v_lams_1310_ = _args[4];
lean_object* v_____r_1311_ = _args[5];
lean_object* v___y_1312_ = _args[6];
lean_object* v___y_1313_ = _args[7];
lean_object* v___y_1314_ = _args[8];
lean_object* v___y_1315_ = _args[9];
lean_object* v___y_1316_ = _args[10];
lean_object* v___y_1317_ = _args[11];
lean_object* v___y_1318_ = _args[12];
lean_object* v___y_1319_ = _args[13];
lean_object* v___y_1320_ = _args[14];
lean_object* v___y_1321_ = _args[15];
lean_object* v___y_1322_ = _args[16];
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1306_, v_a_1307_, v_fst_1308_, v_a_1309_, v_lams_1310_, v_____r_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v_lams_1310_);
lean_dec_ref(v_a_1309_);
lean_dec_ref(v_a_1307_);
return v_res_1323_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1330_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1331_ = l_Lean_Name_append(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_lams_1337_, lean_object* v_a_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___y_1351_; lean_object* v_toCold_1371_; lean_object* v_options_1372_; lean_object* v_fst_1373_; lean_object* v_snd_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1411_; 
v_toCold_1371_ = lean_ctor_get(v___y_1347_, 0);
v_options_1372_ = lean_ctor_get(v_toCold_1371_, 2);
v_fst_1373_ = lean_ctor_get(v_a_1338_, 0);
v_snd_1374_ = lean_ctor_get(v_a_1338_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1338_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1376_ = v_a_1338_;
v_isShared_1377_ = v_isSharedCheck_1411_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_snd_1374_);
lean_inc(v_fst_1373_);
lean_dec(v_a_1338_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1411_;
goto v_resetjp_1375_;
}
v___jp_1350_:
{
if (lean_obj_tag(v___y_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1362_; 
v_a_1352_ = lean_ctor_get(v___y_1351_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___y_1351_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1354_ = v___y_1351_;
v_isShared_1355_ = v_isSharedCheck_1362_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___y_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1362_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
if (lean_obj_tag(v_a_1352_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; 
v_a_1356_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v_a_1352_, 1);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_a_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_object* v_a_1360_; 
lean_del_object(v___x_1354_);
v_a_1360_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v_a_1352_, 1);
v_a_1338_ = v_a_1360_;
goto _start;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___y_1351_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___y_1351_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___y_1351_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___y_1351_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
v_resetjp_1375_:
{
lean_object* v_inheritedTraceOptions_1378_; uint8_t v_hasTrace_1379_; 
v_inheritedTraceOptions_1378_ = lean_ctor_get(v_toCold_1371_, 11);
v_hasTrace_1379_ = lean_ctor_get_uint8(v_options_1372_, sizeof(void*)*1);
if (v_hasTrace_1379_ == 0)
{
lean_del_object(v___x_1376_);
goto v___jp_1380_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1384_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1378_, v_options_1372_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_del_object(v___x_1376_);
goto v___jp_1380_;
}
else
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Meta_Grind_updateLastTag(v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec_ref_known(v___x_1386_, 1);
v___x_1387_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1374_);
v___x_1388_ = l_Lean_MessageData_ofExpr(v_snd_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 7);
lean_ctor_set(v___x_1376_, 1, v___x_1388_);
lean_ctor_set(v___x_1376_, 0, v___x_1387_);
v___x_1390_ = v___x_1376_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1383_, v___x_1390_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1374_, v_a_1335_, v_fst_1373_, v_a_1336_, v_lams_1337_, v_a_1392_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v___y_1351_ = v___x_1393_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_snd_1374_);
lean_dec(v_fst_1373_);
v_a_1394_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1391_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1391_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_del_object(v___x_1376_);
lean_dec(v_snd_1374_);
lean_dec(v_fst_1373_);
v_a_1403_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1386_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1386_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
v___jp_1380_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1374_, v_a_1335_, v_fst_1373_, v_a_1336_, v_lams_1337_, v___x_1381_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v___y_1351_ = v___x_1382_;
goto v___jp_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_lams_1414_, lean_object* v_a_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1412_, v_a_1413_, v_lams_1414_, v_a_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v_lams_1414_);
lean_dec_ref(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1427_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1433_, lean_object* v_lams_1434_, lean_object* v_as_x27_1435_, lean_object* v_b_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
if (lean_obj_tag(v_as_x27_1435_) == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1436_);
return v___x_1448_;
}
else
{
lean_object* v_toCold_1449_; lean_object* v_options_1450_; lean_object* v_head_1451_; lean_object* v_tail_1452_; lean_object* v_inheritedTraceOptions_1453_; uint8_t v_hasTrace_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; 
v_toCold_1449_ = lean_ctor_get(v___y_1445_, 0);
v_options_1450_ = lean_ctor_get(v_toCold_1449_, 2);
v_head_1451_ = lean_ctor_get(v_as_x27_1435_, 0);
v_tail_1452_ = lean_ctor_get(v_as_x27_1435_, 1);
v_inheritedTraceOptions_1453_ = lean_ctor_get(v_toCold_1449_, 11);
v_hasTrace_1454_ = lean_ctor_get_uint8(v_options_1450_, sizeof(void*)*1);
v___x_1455_ = lean_box(0);
v___x_1456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1454_ == 0)
{
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1480_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1453_, v_options_1450_, v___x_1480_);
if (v___x_1481_ == 0)
{
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Meta_Grind_updateLastTag(v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref_known(v___x_1482_, 1);
v___x_1483_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1451_);
v___x_1484_ = l_Lean_MessageData_ofExpr(v_head_1451_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1479_, v___x_1485_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_dec_ref_known(v___x_1486_, 1);
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
goto v___jp_1457_;
}
else
{
return v___x_1486_;
}
}
else
{
return v___x_1482_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_inc(v_head_1451_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1456_);
lean_ctor_set(v___x_1468_, 1, v_head_1451_);
v___x_1469_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1451_, v_a_1433_, v_lams_1434_, v___x_1468_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v_as_x27_1435_ = v_tail_1452_;
v_b_1436_ = v___x_1455_;
goto _start;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1469_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1487_, lean_object* v_lams_1488_, lean_object* v_as_x27_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1487_, v_lams_1488_, v_as_x27_1489_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec(v_as_x27_1489_);
lean_dec_ref(v_lams_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1503_, lean_object* v_lams_1504_, lean_object* v_as_1505_, lean_object* v_as_x27_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
if (lean_obj_tag(v_as_x27_1506_) == 0)
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_b_1507_);
return v___x_1519_;
}
else
{
lean_object* v_toCold_1520_; lean_object* v_options_1521_; lean_object* v_head_1522_; lean_object* v_tail_1523_; lean_object* v_inheritedTraceOptions_1524_; uint8_t v_hasTrace_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; 
v_toCold_1520_ = lean_ctor_get(v___y_1516_, 0);
v_options_1521_ = lean_ctor_get(v_toCold_1520_, 2);
v_head_1522_ = lean_ctor_get(v_as_x27_1506_, 0);
v_tail_1523_ = lean_ctor_get(v_as_x27_1506_, 1);
v_inheritedTraceOptions_1524_ = lean_ctor_get(v_toCold_1520_, 11);
v_hasTrace_1525_ = lean_ctor_get_uint8(v_options_1521_, sizeof(void*)*1);
v___x_1526_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1525_ == 0)
{
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1551_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1552_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1524_, v_options_1521_, v___x_1551_);
if (v___x_1552_ == 0)
{
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Meta_Grind_updateLastTag(v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v___x_1553_, 1);
v___x_1554_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1522_);
v___x_1555_ = l_Lean_MessageData_ofExpr(v_head_1522_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1550_, v___x_1556_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_dec_ref_known(v___x_1557_, 1);
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
goto v___jp_1528_;
}
else
{
return v___x_1557_;
}
}
else
{
return v___x_1553_;
}
}
}
v___jp_1528_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_inc(v_head_1522_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1527_);
lean_ctor_set(v___x_1539_, 1, v_head_1522_);
v___x_1540_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1522_, v_a_1503_, v_lams_1504_, v___x_1539_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v___x_1540_, 1);
v___x_1541_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1503_, v_lams_1504_, v_tail_1523_, v___x_1526_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1541_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1540_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1540_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1558_, lean_object* v_lams_1559_, lean_object* v_as_1560_, lean_object* v_as_x27_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1558_, v_lams_1559_, v_as_1560_, v_as_x27_1561_, v_b_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec(v_as_x27_1561_);
lean_dec(v_as_1560_);
lean_dec_ref(v_lams_1559_);
lean_dec_ref(v_a_1558_);
return v_res_1574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1581_, lean_object* v_lams_1582_, lean_object* v_as_1583_, size_t v_sz_1584_, size_t v_i_1585_, lean_object* v_b_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_lt(v_i_1585_, v_sz_1584_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_b_1586_);
return v___x_1599_;
}
else
{
lean_object* v_toCold_1600_; lean_object* v_options_1601_; lean_object* v_inheritedTraceOptions_1602_; uint8_t v_hasTrace_1603_; lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; 
v_toCold_1600_ = lean_ctor_get(v___y_1595_, 0);
v_options_1601_ = lean_ctor_get(v_toCold_1600_, 2);
v_inheritedTraceOptions_1602_ = lean_ctor_get(v_toCold_1600_, 11);
v_hasTrace_1603_ = lean_ctor_get_uint8(v_options_1601_, sizeof(void*)*1);
v___x_1604_ = lean_box(0);
v_a_1605_ = lean_array_uget_borrowed(v_as_1583_, v_i_1585_);
if (v_hasTrace_1603_ == 0)
{
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1632_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1633_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1602_, v_options_1601_, v___x_1633_);
if (v___x_1634_ == 0)
{
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Meta_Grind_updateLastTag(v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1636_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1605_, v___y_1587_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1605_);
v___x_1639_ = l_Lean_MessageData_ofExpr(v_a_1605_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1637_);
lean_dec(v_a_1637_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1643_, v___x_1644_);
v___x_1646_ = l_Lean_MessageData_ofList(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1642_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1632_, v___x_1647_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_dec_ref_known(v___x_1648_, 1);
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
goto v___jp_1606_;
}
else
{
return v___x_1648_;
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1636_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1636_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
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
else
{
return v___x_1635_;
}
}
}
v___jp_1606_:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1605_, v___y_1607_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1618_);
lean_dec(v_a_1618_);
v___x_1620_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1581_, v_lams_1582_, v___x_1619_, v___x_1619_, v___x_1604_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
size_t v___x_1621_; size_t v___x_1622_; 
lean_dec_ref_known(v___x_1620_, 1);
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_i_1585_, v___x_1621_);
v_i_1585_ = v___x_1622_;
v_b_1586_ = v___x_1604_;
goto _start;
}
else
{
return v___x_1620_;
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1624_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1617_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1617_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1657_ = _args[0];
lean_object* v_lams_1658_ = _args[1];
lean_object* v_as_1659_ = _args[2];
lean_object* v_sz_1660_ = _args[3];
lean_object* v_i_1661_ = _args[4];
lean_object* v_b_1662_ = _args[5];
lean_object* v___y_1663_ = _args[6];
lean_object* v___y_1664_ = _args[7];
lean_object* v___y_1665_ = _args[8];
lean_object* v___y_1666_ = _args[9];
lean_object* v___y_1667_ = _args[10];
lean_object* v___y_1668_ = _args[11];
lean_object* v___y_1669_ = _args[12];
lean_object* v___y_1670_ = _args[13];
lean_object* v___y_1671_ = _args[14];
lean_object* v___y_1672_ = _args[15];
lean_object* v___y_1673_ = _args[16];
_start:
{
size_t v_sz_boxed_1674_; size_t v_i_boxed_1675_; lean_object* v_res_1676_; 
v_sz_boxed_1674_ = lean_unbox_usize(v_sz_1660_);
lean_dec(v_sz_1660_);
v_i_boxed_1675_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1657_, v_lams_1658_, v_as_1659_, v_sz_boxed_1674_, v_i_boxed_1675_, v_b_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v_as_1659_);
lean_dec_ref(v_lams_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1677_, lean_object* v_lams_1678_, lean_object* v_as_1679_, size_t v_sz_1680_, size_t v_i_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1681_, v_sz_1680_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_b_1682_);
return v___x_1695_;
}
else
{
lean_object* v_toCold_1696_; lean_object* v_options_1697_; lean_object* v_inheritedTraceOptions_1698_; uint8_t v_hasTrace_1699_; lean_object* v___x_1700_; lean_object* v_a_1701_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; 
v_toCold_1696_ = lean_ctor_get(v___y_1691_, 0);
v_options_1697_ = lean_ctor_get(v_toCold_1696_, 2);
v_inheritedTraceOptions_1698_ = lean_ctor_get(v_toCold_1696_, 11);
v_hasTrace_1699_ = lean_ctor_get_uint8(v_options_1697_, sizeof(void*)*1);
v___x_1700_ = lean_box(0);
v_a_1701_ = lean_array_uget_borrowed(v_as_1679_, v_i_1681_);
if (v_hasTrace_1699_ == 0)
{
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1728_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1729_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1698_, v_options_1697_, v___x_1729_);
if (v___x_1730_ == 0)
{
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_Grind_updateLastTag(v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref_known(v___x_1731_, 1);
v___x_1732_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1701_, v___y_1683_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1701_);
v___x_1735_ = l_Lean_MessageData_ofExpr(v_a_1701_);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1733_);
lean_dec(v_a_1733_);
v___x_1740_ = lean_box(0);
v___x_1741_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1739_, v___x_1740_);
v___x_1742_ = l_Lean_MessageData_ofList(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1738_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1728_, v___x_1743_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_dec_ref_known(v___x_1744_, 1);
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
goto v___jp_1702_;
}
else
{
return v___x_1744_;
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1732_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1732_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
return v___x_1731_;
}
}
}
v___jp_1702_:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1701_, v___y_1703_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1714_);
lean_dec(v_a_1714_);
v___x_1716_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1677_, v_lams_1678_, v___x_1715_, v___x_1715_, v___x_1700_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___x_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref_known(v___x_1716_, 1);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1681_, v___x_1717_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1677_, v_lams_1678_, v_as_1679_, v_sz_1680_, v___x_1718_, v___x_1700_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1719_;
}
else
{
return v___x_1716_;
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1713_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1713_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1753_ = _args[0];
lean_object* v_lams_1754_ = _args[1];
lean_object* v_as_1755_ = _args[2];
lean_object* v_sz_1756_ = _args[3];
lean_object* v_i_1757_ = _args[4];
lean_object* v_b_1758_ = _args[5];
lean_object* v___y_1759_ = _args[6];
lean_object* v___y_1760_ = _args[7];
lean_object* v___y_1761_ = _args[8];
lean_object* v___y_1762_ = _args[9];
lean_object* v___y_1763_ = _args[10];
lean_object* v___y_1764_ = _args[11];
lean_object* v___y_1765_ = _args[12];
lean_object* v___y_1766_ = _args[13];
lean_object* v___y_1767_ = _args[14];
lean_object* v___y_1768_ = _args[15];
lean_object* v___y_1769_ = _args[16];
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1756_);
lean_dec(v_sz_1756_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1753_, v_lams_1754_, v_as_1755_, v_sz_boxed_1770_, v_i_boxed_1771_, v_b_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v_as_1755_);
lean_dec_ref(v_lams_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1772_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1779_, lean_object* v_fns_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_array_get_size(v_lams_1779_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = l_Lean_instInhabitedExpr;
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_nat_sub(v___x_1792_, v___x_1796_);
v___x_1798_ = lean_array_get_borrowed(v___x_1795_, v_lams_1779_, v___x_1797_);
lean_dec(v___x_1797_);
v___x_1799_ = lean_st_ref_get(v_a_1781_);
lean_inc(v___x_1798_);
v___x_1800_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1799_, v___x_1798_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v_toCold_1825_; lean_object* v_options_1826_; uint8_t v_hasTrace_1827_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v_toCold_1825_ = lean_ctor_get(v_a_1789_, 0);
v_options_1826_ = lean_ctor_get(v_toCold_1825_, 2);
v_hasTrace_1827_ = lean_ctor_get_uint8(v_options_1826_, sizeof(void*)*1);
if (v_hasTrace_1827_ == 0)
{
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
goto v___jp_1802_;
}
else
{
lean_object* v_inheritedTraceOptions_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_inheritedTraceOptions_1828_ = lean_ctor_get(v_toCold_1825_, 11);
v___x_1829_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1830_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1828_, v_options_1826_, v___x_1830_);
if (v___x_1831_ == 0)
{
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Meta_Grind_updateLastTag(v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1832_, 1);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1780_);
v___x_1834_ = lean_array_to_list(v_fns_1780_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1834_, v___x_1835_);
v___x_1837_ = l_Lean_MessageData_ofList(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1833_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
lean_inc_ref(v_lams_1779_);
v___x_1841_ = lean_array_to_list(v_lams_1779_);
v___x_1842_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1841_, v___x_1835_);
v___x_1843_ = l_Lean_MessageData_ofList(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1829_, v___x_1844_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_dec_ref_known(v___x_1845_, 1);
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
goto v___jp_1802_;
}
else
{
lean_dec(v_a_1801_);
lean_dec_ref(v_fns_1780_);
lean_dec_ref(v_lams_1779_);
return v___x_1845_;
}
}
else
{
lean_dec(v_a_1801_);
lean_dec_ref(v_fns_1780_);
lean_dec_ref(v_lams_1779_);
return v___x_1832_;
}
}
}
v___jp_1802_:
{
lean_object* v___x_1813_; size_t v_sz_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_box(0);
v_sz_1814_ = lean_array_size(v_fns_1780_);
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1801_, v_lams_1779_, v_fns_1780_, v_sz_1814_, v___x_1815_, v___x_1813_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v_fns_1780_);
lean_dec_ref(v_lams_1779_);
lean_dec(v_a_1801_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1816_, 0);
lean_dec(v_unused_1824_);
v___x_1818_ = v___x_1816_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_dec(v___x_1816_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1813_);
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1813_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v_fns_1780_);
lean_dec_ref(v_lams_1779_);
v_a_1846_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1800_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1800_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v_fns_1780_);
lean_dec_ref(v_lams_1779_);
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1856_, lean_object* v_fns_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1856_, v_fns_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec(v_a_1858_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_lams_1872_, lean_object* v_inst_1873_, lean_object* v_a_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1870_, v_a_1871_, v_lams_1872_, v_a_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_lams_1889_, lean_object* v_inst_1890_, lean_object* v_a_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1887_, v_a_1888_, v_lams_1889_, v_inst_1890_, v_a_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_lams_1889_);
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1904_, lean_object* v_lams_1905_, lean_object* v_as_1906_, lean_object* v_as_x27_1907_, lean_object* v_b_1908_, lean_object* v_a_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1904_, v_lams_1905_, v_as_1906_, v_as_x27_1907_, v_b_1908_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1922_ = _args[0];
lean_object* v_lams_1923_ = _args[1];
lean_object* v_as_1924_ = _args[2];
lean_object* v_as_x27_1925_ = _args[3];
lean_object* v_b_1926_ = _args[4];
lean_object* v_a_1927_ = _args[5];
lean_object* v___y_1928_ = _args[6];
lean_object* v___y_1929_ = _args[7];
lean_object* v___y_1930_ = _args[8];
lean_object* v___y_1931_ = _args[9];
lean_object* v___y_1932_ = _args[10];
lean_object* v___y_1933_ = _args[11];
lean_object* v___y_1934_ = _args[12];
lean_object* v___y_1935_ = _args[13];
lean_object* v___y_1936_ = _args[14];
lean_object* v___y_1937_ = _args[15];
lean_object* v___y_1938_ = _args[16];
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1922_, v_lams_1923_, v_as_1924_, v_as_x27_1925_, v_b_1926_, v_a_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v_as_x27_1925_);
lean_dec(v_as_1924_);
lean_dec_ref(v_lams_1923_);
lean_dec_ref(v_a_1922_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1940_, lean_object* v_lams_1941_, lean_object* v_as_1942_, lean_object* v_as_x27_1943_, lean_object* v_b_1944_, lean_object* v_a_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1940_, v_lams_1941_, v_as_x27_1943_, v_b_1944_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1958_ = _args[0];
lean_object* v_lams_1959_ = _args[1];
lean_object* v_as_1960_ = _args[2];
lean_object* v_as_x27_1961_ = _args[3];
lean_object* v_b_1962_ = _args[4];
lean_object* v_a_1963_ = _args[5];
lean_object* v___y_1964_ = _args[6];
lean_object* v___y_1965_ = _args[7];
lean_object* v___y_1966_ = _args[8];
lean_object* v___y_1967_ = _args[9];
lean_object* v___y_1968_ = _args[10];
lean_object* v___y_1969_ = _args[11];
lean_object* v___y_1970_ = _args[12];
lean_object* v___y_1971_ = _args[13];
lean_object* v___y_1972_ = _args[14];
lean_object* v___y_1973_ = _args[15];
lean_object* v___y_1974_ = _args[16];
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1958_, v_lams_1959_, v_as_1960_, v_as_x27_1961_, v_b_1962_, v_a_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v_as_x27_1961_);
lean_dec(v_as_1960_);
lean_dec_ref(v_lams_1959_);
lean_dec_ref(v_a_1958_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1979_, lean_object* v_as_1980_, size_t v_sz_1981_, size_t v_i_1982_, lean_object* v_b_1983_){
_start:
{
lean_object* v_a_1985_; uint8_t v___x_1989_; 
v___x_1989_ = lean_usize_dec_lt(v_i_1982_, v_sz_1981_);
if (v___x_1989_ == 0)
{
lean_inc_ref(v_b_1983_);
return v_b_1983_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_a_1992_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1992_ = lean_array_uget_borrowed(v_as_1980_, v_i_1982_);
if (lean_obj_tag(v_a_1992_) == 6)
{
lean_object* v_binderType_1993_; size_t v___x_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v_binderType_1993_ = lean_ctor_get(v_a_1992_, 1);
v___x_1994_ = lean_ptr_addr(v_d_1979_);
v___x_1995_ = lean_ptr_addr(v_binderType_1993_);
v___x_1996_ = lean_usize_dec_eq(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
v_a_1985_ = v___x_1991_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v_a_1992_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_a_1992_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1990_);
return v___x_1999_;
}
}
else
{
v_a_1985_ = v___x_1991_;
goto v___jp_1984_;
}
}
v___jp_1984_:
{
size_t v___x_1986_; size_t v___x_1987_; 
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1982_, v___x_1986_);
v_i_1982_ = v___x_1987_;
v_b_1983_ = v_a_1985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2000_, lean_object* v_as_2001_, lean_object* v_sz_2002_, lean_object* v_i_2003_, lean_object* v_b_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2002_);
lean_dec(v_sz_2002_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2000_, v_as_2001_, v_sz_boxed_2005_, v_i_boxed_2006_, v_b_2004_);
lean_dec_ref(v_b_2004_);
lean_dec_ref(v_as_2001_);
lean_dec_ref(v_d_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2008_, lean_object* v_d_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; size_t v_sz_2012_; size_t v___x_2013_; lean_object* v___x_2014_; lean_object* v_fst_2015_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2012_ = lean_array_size(v_lams_2008_);
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2009_, v_lams_2008_, v_sz_2012_, v___x_2013_, v___x_2011_);
v_fst_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_fst_2015_);
lean_dec_ref(v___x_2014_);
if (lean_obj_tag(v_fst_2015_) == 0)
{
return v___x_2010_;
}
else
{
lean_object* v_val_2016_; 
v_val_2016_ = lean_ctor_get(v_fst_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v_fst_2015_, 1);
return v_val_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2017_, lean_object* v_d_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2017_, v_d_2018_);
lean_dec_ref(v_d_2018_);
lean_dec_ref(v_lams_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2030_, lean_object* v_as_2031_, size_t v_sz_2032_, size_t v_i_2033_, lean_object* v_b_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_a_2047_; uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2033_, v_sz_2032_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2034_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v_a_2054_; 
v___x_2053_ = lean_box(0);
v_a_2054_ = lean_array_uget_borrowed(v_as_2031_, v_i_2033_);
if (lean_obj_tag(v_a_2054_) == 6)
{
lean_object* v_binderType_2055_; lean_object* v_body_2056_; lean_object* v___x_2057_; 
v_binderType_2055_ = lean_ctor_get(v_a_2054_, 1);
v_body_2056_ = lean_ctor_get(v_a_2054_, 2);
lean_inc_ref(v_binderType_2055_);
v___x_2057_ = l_Lean_Meta_getLevel(v_binderType_2055_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_a_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
lean_inc_ref(v___x_2061_);
v___x_2062_ = l_Lean_mkConst(v___x_2059_, v___x_2061_);
lean_inc_ref(v_binderType_2055_);
v___x_2063_ = l_Lean_Expr_app___override(v___x_2062_, v_binderType_2055_);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_Lean_Meta_synthInstance_x3f(v___x_2063_, v___x_2064_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
if (lean_obj_tag(v_a_2066_) == 1)
{
lean_object* v_val_2067_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; uint8_t v___x_2130_; 
v_val_2067_ = lean_ctor_get(v_a_2066_, 0);
lean_inc(v_val_2067_);
lean_dec_ref_known(v_a_2066_, 1);
v___x_2130_ = l_Lean_Expr_hasLooseBVars(v_body_2056_);
if (v___x_2130_ == 0)
{
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
v___y_2077_ = v___y_2043_;
v___y_2078_ = v___y_2044_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2061_);
v___x_2132_ = l_Lean_mkConst(v___x_2131_, v___x_2061_);
lean_inc_ref(v_binderType_2055_);
v___x_2133_ = l_Lean_Expr_app___override(v___x_2132_, v_binderType_2055_);
v___x_2134_ = l_Lean_Meta_synthInstance_x3f(v___x_2133_, v___x_2064_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
if (lean_obj_tag(v_a_2135_) == 0)
{
lean_dec(v_val_2067_);
lean_dec_ref_known(v___x_2061_, 2);
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
else
{
lean_dec_ref_known(v_a_2135_, 1);
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
v___y_2077_ = v___y_2043_;
v___y_2078_ = v___y_2044_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_val_2067_);
lean_dec_ref_known(v___x_2061_, 2);
v_a_2136_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2134_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2134_);
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
v___jp_2068_:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2030_, v_binderType_2055_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v_val_2080_; 
v_val_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v___x_2079_, 1);
if (lean_obj_tag(v_val_2080_) == 6)
{
lean_object* v_body_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_body_2081_ = lean_ctor_get(v_val_2080_, 2);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2083_ = l_Lean_mkConst(v___x_2082_, v___x_2061_);
lean_inc_ref(v_binderType_2055_);
v___x_2084_ = l_Lean_mkAppB(v___x_2083_, v_binderType_2055_, v_val_2067_);
v___x_2085_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2084_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_expr_instantiate1(v_body_2056_, v_a_2086_);
v___x_2088_ = lean_expr_instantiate1(v_body_2081_, v_a_2086_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v_a_2054_);
v___x_2089_ = lean_grind_mk_eq_proof(v_a_2054_, v_val_2080_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Meta_mkCongrFun(v_a_2090_, v_a_2086_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_mkEq(v___x_2087_, v___x_2088_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_Meta_mkExpectedPropHint(v_a_2092_, v_a_2094_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = l_Lean_Meta_Grind_pushNewFact(v___x_2095_, v___x_2096_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_dec_ref_known(v___x_2097_, 1);
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
else
{
return v___x_2097_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_a_2092_);
v_a_2098_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2093_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
v_a_2106_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2091_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2091_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_a_2086_);
v_a_2114_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2089_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2089_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref_known(v_val_2080_, 3);
v_a_2122_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2085_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2085_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_dec(v_val_2080_);
lean_dec(v_val_2067_);
lean_dec_ref_known(v___x_2061_, 2);
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
}
else
{
lean_dec(v___x_2079_);
lean_dec(v_val_2067_);
lean_dec_ref_known(v___x_2061_, 2);
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
}
}
else
{
lean_dec(v_a_2066_);
lean_dec_ref_known(v___x_2061_, 2);
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref_known(v___x_2061_, 2);
v_a_2144_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2065_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2065_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2057_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2057_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
v_a_2047_ = v___x_2053_;
goto v___jp_2046_;
}
}
v___jp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; 
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2033_, v___x_2048_);
v_i_2033_ = v___x_2049_;
v_b_2034_ = v_a_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object* v_lams_u2082_2160_, lean_object* v_as_2161_, lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
size_t v_sz_boxed_2176_; size_t v_i_boxed_2177_; lean_object* v_res_2178_; 
v_sz_boxed_2176_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2177_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2160_, v_as_2161_, v_sz_boxed_2176_, v_i_boxed_2177_, v_b_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v_as_2161_);
lean_dec_ref(v_lams_u2082_2160_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2179_, lean_object* v_lams_u2082_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_array_get_size(v_lams_u2081_2179_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_array_get_size(v_lams_u2082_2180_);
v___x_2199_ = lean_nat_dec_eq(v___x_2198_, v___x_2196_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; size_t v_sz_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = lean_box(0);
v_sz_2201_ = lean_array_size(v_lams_u2081_2179_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2180_, v_lams_u2081_2179_, v_sz_2201_, v___x_2202_, v___x_2200_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2211_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2200_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
return v___x_2203_;
}
}
else
{
goto v___jp_2192_;
}
}
else
{
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2212_, lean_object* v_lams_u2082_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2212_, v_lams_u2082_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_lams_u2082_2213_);
lean_dec_ref(v_lams_u2081_2212_);
return v_res_2225_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2228_){
_start:
{
uint8_t v_res_2229_; lean_object* v_r_2230_; 
v_res_2229_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2228_);
lean_dec_ref(v_x_2228_);
v_r_2230_ = lean_box(v_res_2229_);
return v_r_2230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_){
_start:
{
uint8_t v_res_2236_; lean_object* v_r_2237_; 
v_res_2236_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2234_, v_x_2235_);
lean_dec_ref(v_x_2235_);
v_r_2237_ = lean_box(v_res_2236_);
return v_r_2237_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2238_, lean_object* v_v_2239_, lean_object* v_i_2240_){
_start:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_array_get_size(v_xs_2238_);
v___x_2242_ = lean_nat_dec_lt(v_i_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_i_2240_);
v___x_2243_ = lean_box(0);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2244_ = lean_array_fget_borrowed(v_xs_2238_, v_i_2240_);
v___x_2245_ = lean_ptr_addr(v___x_2244_);
v___x_2246_ = lean_ptr_addr(v_v_2239_);
v___x_2247_ = lean_usize_dec_eq(v___x_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v_i_2240_, v___x_2248_);
lean_dec(v_i_2240_);
v_i_2240_ = v___x_2249_;
goto _start;
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_i_2240_);
return v___x_2251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2252_, lean_object* v_v_2253_, lean_object* v_i_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2252_, v_v_2253_, v_i_2254_);
lean_dec_ref(v_v_2253_);
lean_dec_ref(v_xs_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2256_, lean_object* v_v_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2256_, v_v_2257_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2260_, lean_object* v_v_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2260_, v_v_2261_);
lean_dec_ref(v_v_2261_);
lean_dec_ref(v_xs_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2263_, size_t v_x_2264_, lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 0)
{
lean_object* v_es_2266_; lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; lean_object* v_j_2270_; lean_object* v_entry_2271_; 
v_es_2266_ = lean_ctor_get(v_x_2263_, 0);
v___x_2267_ = lean_box(2);
v___x_2268_ = ((size_t)31ULL);
v___x_2269_ = lean_usize_land(v_x_2264_, v___x_2268_);
v_j_2270_ = lean_usize_to_nat(v___x_2269_);
v_entry_2271_ = lean_array_get(v___x_2267_, v_es_2266_, v_j_2270_);
switch(lean_obj_tag(v_entry_2271_))
{
case 0:
{
lean_object* v_key_2272_; size_t v___x_2273_; size_t v___x_2274_; uint8_t v___x_2275_; 
v_key_2272_ = lean_ctor_get(v_entry_2271_, 0);
lean_inc(v_key_2272_);
lean_dec_ref_known(v_entry_2271_, 2);
v___x_2273_ = lean_ptr_addr(v_x_2265_);
v___x_2274_ = lean_ptr_addr(v_key_2272_);
lean_dec(v_key_2272_);
v___x_2275_ = lean_usize_dec_eq(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec(v_j_2270_);
return v_x_2263_;
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
lean_inc_ref(v_es_2266_);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_x_2263_, 0);
lean_dec(v_unused_2284_);
v___x_2277_ = v_x_2263_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2263_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_array_set(v_es_2266_, v_j_2270_, v___x_2267_);
lean_dec(v_j_2270_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
case 1:
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2319_; 
lean_inc_ref(v_es_2266_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_x_2263_, 0);
lean_dec(v_unused_2320_);
v___x_2286_ = v_x_2263_;
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_x_2263_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_node_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2318_; 
v_node_2288_ = lean_ctor_get(v_entry_2271_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_entry_2271_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2290_ = v_entry_2271_;
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_node_2288_);
lean_dec(v_entry_2271_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
size_t v___x_2292_; lean_object* v_entries_2293_; size_t v___x_2294_; lean_object* v_newNode_2295_; lean_object* v___x_2296_; 
v___x_2292_ = ((size_t)5ULL);
v_entries_2293_ = lean_array_set(v_es_2266_, v_j_2270_, v___x_2267_);
v___x_2294_ = lean_usize_shift_right(v_x_2264_, v___x_2292_);
v_newNode_2295_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2288_, v___x_2294_, v_x_2265_);
lean_inc_ref(v_newNode_2295_);
v___x_2296_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2298_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_newNode_2295_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_newNode_2295_);
v___x_2298_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = lean_array_set(v_entries_2293_, v_j_2270_, v___x_2298_);
lean_dec(v_j_2270_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2299_);
v___x_2301_ = v___x_2286_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_object* v_val_2304_; lean_object* v_fst_2305_; lean_object* v_snd_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_newNode_2295_);
lean_del_object(v___x_2290_);
v_val_2304_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2296_, 1);
v_fst_2305_ = lean_ctor_get(v_val_2304_, 0);
v_snd_2306_ = lean_ctor_get(v_val_2304_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_val_2304_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2308_ = v_val_2304_;
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snd_2306_);
lean_inc(v_fst_2305_);
lean_dec(v_val_2304_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2317_;
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
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_snd_2306_);
v___x_2311_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2312_ = lean_array_set(v_entries_2293_, v_j_2270_, v___x_2311_);
lean_dec(v_j_2270_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2312_);
v___x_2314_ = v___x_2286_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2270_);
return v_x_2263_;
}
}
}
else
{
lean_object* v_ks_2321_; lean_object* v_vs_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_ks_2321_ = lean_ctor_get(v_x_2263_, 0);
v_vs_2322_ = lean_ctor_get(v_x_2263_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2324_ = v_x_2263_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_vs_2322_);
lean_inc(v_ks_2321_);
lean_dec(v_x_2263_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2321_, v_x_2265_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2328_; 
if (v_isShared_2325_ == 0)
{
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_ks_2321_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_vs_2322_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_object* v_val_2330_; lean_object* v_keys_x27_2331_; lean_object* v_vals_x27_2332_; lean_object* v___x_2334_; 
v_val_2330_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_n(v_val_2330_, 2);
lean_dec_ref_known(v___x_2326_, 1);
v_keys_x27_2331_ = l_Array_eraseIdx___redArg(v_ks_2321_, v_val_2330_);
v_vals_x27_2332_ = l_Array_eraseIdx___redArg(v_vs_2322_, v_val_2330_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v_vals_x27_2332_);
lean_ctor_set(v___x_2324_, 0, v_keys_x27_2331_);
v___x_2334_ = v___x_2324_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_keys_x27_2331_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_vals_x27_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_19693__boxed_2340_; lean_object* v_res_2341_; 
v_x_19693__boxed_2340_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2341_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2337_, v_x_19693__boxed_2340_, v_x_2339_);
lean_dec_ref(v_x_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
size_t v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; uint64_t v___x_2347_; size_t v_h_2348_; lean_object* v___x_2349_; 
v___x_2344_ = lean_ptr_addr(v_x_2343_);
v___x_2345_ = ((size_t)3ULL);
v___x_2346_ = lean_usize_shift_right(v___x_2344_, v___x_2345_);
v___x_2347_ = lean_usize_to_uint64(v___x_2346_);
v_h_2348_ = lean_uint64_to_usize(v___x_2347_);
v___x_2349_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2342_, v_h_2348_, v_x_2343_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2350_, lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2350_, v_x_2351_);
lean_dec_ref(v_x_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
if (lean_obj_tag(v_as_2353_) == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
else
{
lean_object* v_head_2367_; lean_object* v_tail_2368_; lean_object* v___x_2369_; 
v_head_2367_ = lean_ctor_get(v_as_2353_, 0);
lean_inc(v_head_2367_);
v_tail_2368_ = lean_ctor_get(v_as_2353_, 1);
lean_inc(v_tail_2368_);
lean_dec_ref_known(v_as_2353_, 2);
v___x_2369_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2367_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref_known(v___x_2369_, 1);
v_as_2353_ = v_tail_2368_;
goto _start;
}
else
{
lean_dec(v_tail_2368_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2384_, lean_object* v_vals_2385_, lean_object* v_i_2386_, lean_object* v_k_2387_){
_start:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = lean_array_get_size(v_keys_2384_);
v___x_2389_ = lean_nat_dec_lt(v_i_2386_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
lean_dec(v_i_2386_);
v___x_2390_ = lean_box(0);
return v___x_2390_;
}
else
{
lean_object* v_k_x27_2391_; size_t v___x_2392_; size_t v___x_2393_; uint8_t v___x_2394_; 
v_k_x27_2391_ = lean_array_fget_borrowed(v_keys_2384_, v_i_2386_);
v___x_2392_ = lean_ptr_addr(v_k_2387_);
v___x_2393_ = lean_ptr_addr(v_k_x27_2391_);
v___x_2394_ = lean_usize_dec_eq(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_nat_add(v_i_2386_, v___x_2395_);
lean_dec(v_i_2386_);
v_i_2386_ = v___x_2396_;
goto _start;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_array_fget_borrowed(v_vals_2385_, v_i_2386_);
lean_dec(v_i_2386_);
lean_inc(v___x_2398_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2400_, lean_object* v_vals_2401_, lean_object* v_i_2402_, lean_object* v_k_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2400_, v_vals_2401_, v_i_2402_, v_k_2403_);
lean_dec_ref(v_k_2403_);
lean_dec_ref(v_vals_2401_);
lean_dec_ref(v_keys_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2405_, size_t v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
lean_object* v_es_2408_; lean_object* v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; lean_object* v_j_2412_; lean_object* v___x_2413_; 
v_es_2408_ = lean_ctor_get(v_x_2405_, 0);
v___x_2409_ = lean_box(2);
v___x_2410_ = ((size_t)31ULL);
v___x_2411_ = lean_usize_land(v_x_2406_, v___x_2410_);
v_j_2412_ = lean_usize_to_nat(v___x_2411_);
v___x_2413_ = lean_array_get_borrowed(v___x_2409_, v_es_2408_, v_j_2412_);
lean_dec(v_j_2412_);
switch(lean_obj_tag(v___x_2413_))
{
case 0:
{
lean_object* v_key_2414_; lean_object* v_val_2415_; size_t v___x_2416_; size_t v___x_2417_; uint8_t v___x_2418_; 
v_key_2414_ = lean_ctor_get(v___x_2413_, 0);
v_val_2415_ = lean_ctor_get(v___x_2413_, 1);
v___x_2416_ = lean_ptr_addr(v_x_2407_);
v___x_2417_ = lean_ptr_addr(v_key_2414_);
v___x_2418_ = lean_usize_dec_eq(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; 
lean_inc(v_val_2415_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_val_2415_);
return v___x_2420_;
}
}
case 1:
{
lean_object* v_node_2421_; size_t v___x_2422_; size_t v___x_2423_; 
v_node_2421_ = lean_ctor_get(v___x_2413_, 0);
v___x_2422_ = ((size_t)5ULL);
v___x_2423_ = lean_usize_shift_right(v_x_2406_, v___x_2422_);
v_x_2405_ = v_node_2421_;
v_x_2406_ = v___x_2423_;
goto _start;
}
default: 
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_box(0);
return v___x_2425_;
}
}
}
else
{
lean_object* v_ks_2426_; lean_object* v_vs_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_ks_2426_ = lean_ctor_get(v_x_2405_, 0);
v_vs_2427_ = lean_ctor_get(v_x_2405_, 1);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2426_, v_vs_2427_, v___x_2428_, v_x_2407_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
size_t v_x_19918__boxed_2433_; lean_object* v_res_2434_; 
v_x_19918__boxed_2433_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_res_2434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2430_, v_x_19918__boxed_2433_, v_x_2432_);
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_x_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; uint64_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = lean_ptr_addr(v_x_2436_);
v___x_2438_ = ((size_t)3ULL);
v___x_2439_ = lean_usize_shift_right(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_usize_to_uint64(v___x_2439_);
v___x_2441_ = lean_uint64_to_usize(v___x_2440_);
v___x_2442_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2435_, v___x_2441_, v_x_2436_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2443_, v_x_2444_);
lean_dec_ref(v_x_2444_);
lean_dec_ref(v_x_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2446_, lean_object* v_b_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
if (lean_obj_tag(v_as_x27_2446_) == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_b_2447_);
return v___x_2459_;
}
else
{
lean_object* v_head_2460_; lean_object* v_tail_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_toGoalState_2464_; lean_object* v_ematch_2465_; lean_object* v_delayedThmInsts_2466_; lean_object* v___x_2467_; 
v_head_2460_ = lean_ctor_get(v_as_x27_2446_, 0);
v_tail_2461_ = lean_ctor_get(v_as_x27_2446_, 1);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_st_ref_get(v___y_2448_);
v_toGoalState_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_toGoalState_2464_);
lean_dec(v___x_2463_);
v_ematch_2465_ = lean_ctor_get(v_toGoalState_2464_, 13);
lean_inc_ref(v_ematch_2465_);
lean_dec_ref(v_toGoalState_2464_);
v_delayedThmInsts_2466_ = lean_ctor_get(v_ematch_2465_, 10);
lean_inc_ref(v_delayedThmInsts_2466_);
lean_dec_ref(v_ematch_2465_);
v___x_2467_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2466_, v_head_2460_);
lean_dec_ref(v_delayedThmInsts_2466_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v_val_2468_; lean_object* v___x_2469_; lean_object* v_toGoalState_2470_; lean_object* v_ematch_2471_; lean_object* v_mvarId_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2530_; 
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = lean_st_ref_take(v___y_2448_);
v_toGoalState_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_toGoalState_2470_);
v_ematch_2471_ = lean_ctor_get(v_toGoalState_2470_, 13);
lean_inc_ref(v_ematch_2471_);
v_mvarId_2472_ = lean_ctor_get(v___x_2469_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2531_);
v___x_2474_ = v___x_2469_;
v_isShared_2475_ = v_isSharedCheck_2530_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_mvarId_2472_);
lean_dec(v___x_2469_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2530_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_nextDeclIdx_2476_; lean_object* v_enodeMap_2477_; lean_object* v_exprs_2478_; lean_object* v_parents_2479_; lean_object* v_congrTable_2480_; lean_object* v_appMap_2481_; lean_object* v_indicesFound_2482_; lean_object* v_toProcess_2483_; lean_object* v_internalizing_2484_; uint8_t v_inconsistent_2485_; lean_object* v_nextIdx_2486_; lean_object* v_newRawFacts_2487_; lean_object* v_facts_2488_; lean_object* v_extThms_2489_; lean_object* v_inj_2490_; lean_object* v_split_2491_; lean_object* v_clean_2492_; lean_object* v_sstates_2493_; lean_object* v_goalStack_2494_; uint64_t v_introBase_2495_; lean_object* v_numIntros_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2528_; 
v_nextDeclIdx_2476_ = lean_ctor_get(v_toGoalState_2470_, 0);
v_enodeMap_2477_ = lean_ctor_get(v_toGoalState_2470_, 1);
v_exprs_2478_ = lean_ctor_get(v_toGoalState_2470_, 2);
v_parents_2479_ = lean_ctor_get(v_toGoalState_2470_, 3);
v_congrTable_2480_ = lean_ctor_get(v_toGoalState_2470_, 4);
v_appMap_2481_ = lean_ctor_get(v_toGoalState_2470_, 5);
v_indicesFound_2482_ = lean_ctor_get(v_toGoalState_2470_, 6);
v_toProcess_2483_ = lean_ctor_get(v_toGoalState_2470_, 7);
v_internalizing_2484_ = lean_ctor_get(v_toGoalState_2470_, 8);
v_inconsistent_2485_ = lean_ctor_get_uint8(v_toGoalState_2470_, sizeof(void*)*20 + 8);
v_nextIdx_2486_ = lean_ctor_get(v_toGoalState_2470_, 9);
v_newRawFacts_2487_ = lean_ctor_get(v_toGoalState_2470_, 10);
v_facts_2488_ = lean_ctor_get(v_toGoalState_2470_, 11);
v_extThms_2489_ = lean_ctor_get(v_toGoalState_2470_, 12);
v_inj_2490_ = lean_ctor_get(v_toGoalState_2470_, 14);
v_split_2491_ = lean_ctor_get(v_toGoalState_2470_, 15);
v_clean_2492_ = lean_ctor_get(v_toGoalState_2470_, 16);
v_sstates_2493_ = lean_ctor_get(v_toGoalState_2470_, 17);
v_goalStack_2494_ = lean_ctor_get(v_toGoalState_2470_, 18);
v_introBase_2495_ = lean_ctor_get_uint64(v_toGoalState_2470_, sizeof(void*)*20);
v_numIntros_2496_ = lean_ctor_get(v_toGoalState_2470_, 19);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_toGoalState_2470_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_toGoalState_2470_, 13);
lean_dec(v_unused_2529_);
v___x_2498_ = v_toGoalState_2470_;
v_isShared_2499_ = v_isSharedCheck_2528_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_numIntros_2496_);
lean_inc(v_goalStack_2494_);
lean_inc(v_sstates_2493_);
lean_inc(v_clean_2492_);
lean_inc(v_split_2491_);
lean_inc(v_inj_2490_);
lean_inc(v_extThms_2489_);
lean_inc(v_facts_2488_);
lean_inc(v_newRawFacts_2487_);
lean_inc(v_nextIdx_2486_);
lean_inc(v_internalizing_2484_);
lean_inc(v_toProcess_2483_);
lean_inc(v_indicesFound_2482_);
lean_inc(v_appMap_2481_);
lean_inc(v_congrTable_2480_);
lean_inc(v_parents_2479_);
lean_inc(v_exprs_2478_);
lean_inc(v_enodeMap_2477_);
lean_inc(v_nextDeclIdx_2476_);
lean_dec(v_toGoalState_2470_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2528_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_thmMap_2500_; lean_object* v_gmt_2501_; lean_object* v_thms_2502_; lean_object* v_newThms_2503_; lean_object* v_numInstances_2504_; lean_object* v_numDelayedInstances_2505_; lean_object* v_num_2506_; lean_object* v_preInstances_2507_; lean_object* v_nextThmIdx_2508_; lean_object* v_matchEqNames_2509_; lean_object* v_delayedThmInsts_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2527_; 
v_thmMap_2500_ = lean_ctor_get(v_ematch_2471_, 0);
v_gmt_2501_ = lean_ctor_get(v_ematch_2471_, 1);
v_thms_2502_ = lean_ctor_get(v_ematch_2471_, 2);
v_newThms_2503_ = lean_ctor_get(v_ematch_2471_, 3);
v_numInstances_2504_ = lean_ctor_get(v_ematch_2471_, 4);
v_numDelayedInstances_2505_ = lean_ctor_get(v_ematch_2471_, 5);
v_num_2506_ = lean_ctor_get(v_ematch_2471_, 6);
v_preInstances_2507_ = lean_ctor_get(v_ematch_2471_, 7);
v_nextThmIdx_2508_ = lean_ctor_get(v_ematch_2471_, 8);
v_matchEqNames_2509_ = lean_ctor_get(v_ematch_2471_, 9);
v_delayedThmInsts_2510_ = lean_ctor_get(v_ematch_2471_, 10);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_ematch_2471_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2512_ = v_ematch_2471_;
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
lean_dec(v_ematch_2471_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2527_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2514_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2510_, v_head_2460_);
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
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_nextDeclIdx_2476_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_enodeMap_2477_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_exprs_2478_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_parents_2479_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_congrTable_2480_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v_appMap_2481_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_indicesFound_2482_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_toProcess_2483_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_internalizing_2484_);
lean_ctor_set(v_reuseFailAlloc_2525_, 9, v_nextIdx_2486_);
lean_ctor_set(v_reuseFailAlloc_2525_, 10, v_newRawFacts_2487_);
lean_ctor_set(v_reuseFailAlloc_2525_, 11, v_facts_2488_);
lean_ctor_set(v_reuseFailAlloc_2525_, 12, v_extThms_2489_);
lean_ctor_set(v_reuseFailAlloc_2525_, 13, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2525_, 14, v_inj_2490_);
lean_ctor_set(v_reuseFailAlloc_2525_, 15, v_split_2491_);
lean_ctor_set(v_reuseFailAlloc_2525_, 16, v_clean_2492_);
lean_ctor_set(v_reuseFailAlloc_2525_, 17, v_sstates_2493_);
lean_ctor_set(v_reuseFailAlloc_2525_, 18, v_goalStack_2494_);
lean_ctor_set(v_reuseFailAlloc_2525_, 19, v_numIntros_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2525_, sizeof(void*)*20 + 8, v_inconsistent_2485_);
lean_ctor_set_uint64(v_reuseFailAlloc_2525_, sizeof(void*)*20, v_introBase_2495_);
v___x_2518_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2518_);
v___x_2520_ = v___x_2474_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_mvarId_2472_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_st_ref_put(v___y_2448_, v___x_2520_);
v___x_2522_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2468_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref_known(v___x_2522_, 1);
v_as_x27_2446_ = v_tail_2461_;
v_b_2447_ = v___x_2462_;
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
lean_dec(v___x_2467_);
v_as_x27_2446_ = v_tail_2461_;
v_b_2447_ = v___x_2462_;
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
size_t v_x_20223__boxed_2667_; lean_object* v_res_2668_; 
v_x_20223__boxed_2667_ = lean_unbox_usize(v_x_2665_);
lean_dec(v_x_2665_);
v_res_2668_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2663_, v_x_2664_, v_x_20223__boxed_2667_, v_x_2666_);
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
size_t v_x_20234__boxed_2678_; lean_object* v_res_2679_; 
v_x_20234__boxed_2678_ = lean_unbox_usize(v_x_2676_);
lean_dec(v_x_2676_);
v_res_2679_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2674_, v_x_2675_, v_x_20234__boxed_2678_, v_x_2677_);
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
size_t v_x_26503__boxed_2745_; lean_object* v_res_2746_; 
v_x_26503__boxed_2745_ = lean_unbox_usize(v_x_2743_);
lean_dec(v_x_2743_);
v_res_2746_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2741_, v_x_2742_, v_x_26503__boxed_2745_, v_x_2744_);
lean_dec_ref(v___x_2741_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
uint64_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
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
lean_inc(v_k_2886_);
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
size_t v_x_26657__boxed_2913_; size_t v_x_26658__boxed_2914_; lean_object* v_res_2915_; 
v_x_26657__boxed_2913_ = lean_unbox_usize(v_x_2909_);
lean_dec(v_x_2909_);
v_x_26658__boxed_2914_ = lean_unbox_usize(v_x_2910_);
lean_dec(v_x_2910_);
v_res_2915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2907_, v_x_2908_, v_x_26657__boxed_2913_, v_x_26658__boxed_2914_, v_x_2911_, v_x_2912_);
lean_dec_ref(v___x_2907_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
uint64_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
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
lean_object* v_snd_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3132_; 
v_snd_2944_ = lean_ctor_get(v_a_2936_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_a_2936_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v_a_2936_, 0);
lean_dec(v_unused_3133_);
v___x_2946_ = v_a_2936_;
v_isShared_2947_ = v_isSharedCheck_3132_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_snd_2944_);
lean_dec(v_a_2936_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3132_;
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
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3123_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_3123_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3123_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_self_2955_; lean_object* v_next_2956_; lean_object* v_congr_2957_; lean_object* v_target_x3f_2958_; lean_object* v_proof_x3f_2959_; uint8_t v_flipped_2960_; lean_object* v_size_2961_; uint8_t v_interpreted_2962_; uint8_t v_ctor_2963_; uint8_t v_hasLambdas_2964_; uint8_t v_heqProofs_2965_; lean_object* v_idx_2966_; lean_object* v_generation_2967_; lean_object* v_mt_2968_; lean_object* v_sTerms_2969_; uint8_t v_funCC_2970_; lean_object* v_ematchDiagSource_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3121_; 
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
v_isSharedCheck_3121_ = !lean_is_exclusive(v_a_2951_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v_a_2951_, 2);
lean_dec(v_unused_3122_);
v___x_2973_ = v_a_2951_;
v_isShared_2974_ = v_isSharedCheck_3121_;
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
v_isShared_2974_ = v_isSharedCheck_3121_;
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
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_self_2955_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_next_2956_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_rootNew_2934_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_congr_2957_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_target_x3f_2958_);
lean_ctor_set(v_reuseFailAlloc_3120_, 5, v_proof_x3f_2959_);
lean_ctor_set(v_reuseFailAlloc_3120_, 6, v_size_2961_);
lean_ctor_set(v_reuseFailAlloc_3120_, 7, v_idx_2966_);
lean_ctor_set(v_reuseFailAlloc_3120_, 8, v_generation_2967_);
lean_ctor_set(v_reuseFailAlloc_3120_, 9, v_mt_2968_);
lean_ctor_set(v_reuseFailAlloc_3120_, 10, v_sTerms_2969_);
lean_ctor_set(v_reuseFailAlloc_3120_, 11, v_ematchDiagSource_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12, v_flipped_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12 + 1, v_interpreted_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12 + 2, v_ctor_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12 + 3, v_hasLambdas_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12 + 4, v_heqProofs_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*12 + 5, v_funCC_2970_);
v___x_2991_ = v_reuseFailAlloc_3120_;
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
lean_object* v___x_3007_; lean_object* v_toGoalState_3008_; lean_object* v_mvarId_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3103_; 
v___x_3007_ = lean_st_ref_take(v___y_2937_);
v_toGoalState_3008_ = lean_ctor_get(v___x_3007_, 0);
v_mvarId_3009_ = lean_ctor_get(v___x_3007_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3011_ = v___x_3007_;
v_isShared_3012_ = v_isSharedCheck_3103_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_mvarId_3009_);
lean_inc(v_toGoalState_3008_);
lean_dec(v___x_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3103_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v_nextDeclIdx_3013_; lean_object* v_enodeMap_3014_; lean_object* v_exprs_3015_; lean_object* v_parents_3016_; lean_object* v_congrTable_3017_; lean_object* v_appMap_3018_; lean_object* v_indicesFound_3019_; lean_object* v_toProcess_3020_; lean_object* v_internalizing_3021_; uint8_t v_inconsistent_3022_; lean_object* v_nextIdx_3023_; lean_object* v_newRawFacts_3024_; lean_object* v_facts_3025_; lean_object* v_extThms_3026_; lean_object* v_ematch_3027_; lean_object* v_inj_3028_; lean_object* v_split_3029_; lean_object* v_clean_3030_; lean_object* v_sstates_3031_; lean_object* v_goalStack_3032_; uint64_t v_introBase_3033_; lean_object* v_numIntros_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3102_; 
v_nextDeclIdx_3013_ = lean_ctor_get(v_toGoalState_3008_, 0);
v_enodeMap_3014_ = lean_ctor_get(v_toGoalState_3008_, 1);
v_exprs_3015_ = lean_ctor_get(v_toGoalState_3008_, 2);
v_parents_3016_ = lean_ctor_get(v_toGoalState_3008_, 3);
v_congrTable_3017_ = lean_ctor_get(v_toGoalState_3008_, 4);
v_appMap_3018_ = lean_ctor_get(v_toGoalState_3008_, 5);
v_indicesFound_3019_ = lean_ctor_get(v_toGoalState_3008_, 6);
v_toProcess_3020_ = lean_ctor_get(v_toGoalState_3008_, 7);
v_internalizing_3021_ = lean_ctor_get(v_toGoalState_3008_, 8);
v_inconsistent_3022_ = lean_ctor_get_uint8(v_toGoalState_3008_, sizeof(void*)*20 + 8);
v_nextIdx_3023_ = lean_ctor_get(v_toGoalState_3008_, 9);
v_newRawFacts_3024_ = lean_ctor_get(v_toGoalState_3008_, 10);
v_facts_3025_ = lean_ctor_get(v_toGoalState_3008_, 11);
v_extThms_3026_ = lean_ctor_get(v_toGoalState_3008_, 12);
v_ematch_3027_ = lean_ctor_get(v_toGoalState_3008_, 13);
v_inj_3028_ = lean_ctor_get(v_toGoalState_3008_, 14);
v_split_3029_ = lean_ctor_get(v_toGoalState_3008_, 15);
v_clean_3030_ = lean_ctor_get(v_toGoalState_3008_, 16);
v_sstates_3031_ = lean_ctor_get(v_toGoalState_3008_, 17);
v_goalStack_3032_ = lean_ctor_get(v_toGoalState_3008_, 18);
v_introBase_3033_ = lean_ctor_get_uint64(v_toGoalState_3008_, sizeof(void*)*20);
v_numIntros_3034_ = lean_ctor_get(v_toGoalState_3008_, 19);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_toGoalState_3008_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3036_ = v_toGoalState_3008_;
v_isShared_3037_ = v_isSharedCheck_3102_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_numIntros_3034_);
lean_inc(v_goalStack_3032_);
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
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3102_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3038_ = lean_box(0);
lean_inc_ref(v_self_2955_);
v___x_3039_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3014_, v_congrTable_3017_, v_self_2955_, v___x_3038_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 4, v___x_3039_);
v___x_3041_ = v___x_3036_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_nextDeclIdx_3013_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_enodeMap_3014_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_exprs_3015_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_parents_3016_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3101_, 5, v_appMap_3018_);
lean_ctor_set(v_reuseFailAlloc_3101_, 6, v_indicesFound_3019_);
lean_ctor_set(v_reuseFailAlloc_3101_, 7, v_toProcess_3020_);
lean_ctor_set(v_reuseFailAlloc_3101_, 8, v_internalizing_3021_);
lean_ctor_set(v_reuseFailAlloc_3101_, 9, v_nextIdx_3023_);
lean_ctor_set(v_reuseFailAlloc_3101_, 10, v_newRawFacts_3024_);
lean_ctor_set(v_reuseFailAlloc_3101_, 11, v_facts_3025_);
lean_ctor_set(v_reuseFailAlloc_3101_, 12, v_extThms_3026_);
lean_ctor_set(v_reuseFailAlloc_3101_, 13, v_ematch_3027_);
lean_ctor_set(v_reuseFailAlloc_3101_, 14, v_inj_3028_);
lean_ctor_set(v_reuseFailAlloc_3101_, 15, v_split_3029_);
lean_ctor_set(v_reuseFailAlloc_3101_, 16, v_clean_3030_);
lean_ctor_set(v_reuseFailAlloc_3101_, 17, v_sstates_3031_);
lean_ctor_set(v_reuseFailAlloc_3101_, 18, v_goalStack_3032_);
lean_ctor_set(v_reuseFailAlloc_3101_, 19, v_numIntros_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*20 + 8, v_inconsistent_3022_);
lean_ctor_set_uint64(v_reuseFailAlloc_3101_, sizeof(void*)*20, v_introBase_3033_);
v___x_3041_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3041_);
v___x_3043_ = v___x_3011_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_mvarId_3009_);
v___x_3043_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_st_ref_put(v___y_2937_, v___x_3043_);
lean_inc_ref(v_rootNew_2934_);
lean_inc_ref(v_next_2956_);
lean_inc_ref_n(v_self_2955_, 3);
v___x_3045_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3045_, 0, v_self_2955_);
lean_ctor_set(v___x_3045_, 1, v_next_2956_);
lean_ctor_set(v___x_3045_, 2, v_rootNew_2934_);
lean_ctor_set(v___x_3045_, 3, v_self_2955_);
lean_ctor_set(v___x_3045_, 4, v_target_x3f_2958_);
lean_ctor_set(v___x_3045_, 5, v_proof_x3f_2959_);
lean_ctor_set(v___x_3045_, 6, v_size_2961_);
lean_ctor_set(v___x_3045_, 7, v_idx_2966_);
lean_ctor_set(v___x_3045_, 8, v_generation_2967_);
lean_ctor_set(v___x_3045_, 9, v_mt_2968_);
lean_ctor_set(v___x_3045_, 10, v_sTerms_2969_);
lean_ctor_set(v___x_3045_, 11, v_ematchDiagSource_2971_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12, v_flipped_2960_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12 + 1, v_interpreted_2962_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12 + 2, v_ctor_2963_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12 + 3, v_hasLambdas_2964_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12 + 4, v_heqProofs_2965_);
lean_ctor_set_uint8(v___x_3045_, sizeof(void*)*12 + 5, v_funCC_2970_);
v___x_3046_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2955_, v___x_3045_, v___y_2937_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref_known(v___x_3046_, 1);
v___x_3047_ = lean_st_ref_get(v___y_2937_);
lean_inc(v_fst_3003_);
v___x_3048_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3047_, v_fst_3003_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_self_3050_; lean_object* v_next_3051_; lean_object* v_root_3052_; lean_object* v_target_x3f_3053_; lean_object* v_proof_x3f_3054_; uint8_t v_flipped_3055_; lean_object* v_size_3056_; uint8_t v_interpreted_3057_; uint8_t v_ctor_3058_; uint8_t v_hasLambdas_3059_; uint8_t v_heqProofs_3060_; lean_object* v_idx_3061_; lean_object* v_generation_3062_; lean_object* v_mt_3063_; lean_object* v_sTerms_3064_; uint8_t v_funCC_3065_; lean_object* v_ematchDiagSource_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3082_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_self_3050_ = lean_ctor_get(v_a_3049_, 0);
v_next_3051_ = lean_ctor_get(v_a_3049_, 1);
v_root_3052_ = lean_ctor_get(v_a_3049_, 2);
v_target_x3f_3053_ = lean_ctor_get(v_a_3049_, 4);
v_proof_x3f_3054_ = lean_ctor_get(v_a_3049_, 5);
v_flipped_3055_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12);
v_size_3056_ = lean_ctor_get(v_a_3049_, 6);
v_interpreted_3057_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12 + 1);
v_ctor_3058_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12 + 2);
v_hasLambdas_3059_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12 + 3);
v_heqProofs_3060_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12 + 4);
v_idx_3061_ = lean_ctor_get(v_a_3049_, 7);
v_generation_3062_ = lean_ctor_get(v_a_3049_, 8);
v_mt_3063_ = lean_ctor_get(v_a_3049_, 9);
v_sTerms_3064_ = lean_ctor_get(v_a_3049_, 10);
v_funCC_3065_ = lean_ctor_get_uint8(v_a_3049_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3066_ = lean_ctor_get(v_a_3049_, 11);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3049_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_a_3049_, 3);
lean_dec(v_unused_3083_);
v___x_3068_ = v_a_3049_;
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_ematchDiagSource_3066_);
lean_inc(v_sTerms_3064_);
lean_inc(v_mt_3063_);
lean_inc(v_generation_3062_);
lean_inc(v_idx_3061_);
lean_inc(v_size_3056_);
lean_inc(v_proof_x3f_3054_);
lean_inc(v_target_x3f_3053_);
lean_inc(v_root_3052_);
lean_inc(v_next_3051_);
lean_inc(v_self_3050_);
lean_dec(v_a_3049_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3082_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 3, v_self_2955_);
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_self_3050_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_next_3051_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_root_3052_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_self_2955_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_target_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3081_, 5, v_proof_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3081_, 6, v_size_3056_);
lean_ctor_set(v_reuseFailAlloc_3081_, 7, v_idx_3061_);
lean_ctor_set(v_reuseFailAlloc_3081_, 8, v_generation_3062_);
lean_ctor_set(v_reuseFailAlloc_3081_, 9, v_mt_3063_);
lean_ctor_set(v_reuseFailAlloc_3081_, 10, v_sTerms_3064_);
lean_ctor_set(v_reuseFailAlloc_3081_, 11, v_ematchDiagSource_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12, v_flipped_3055_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 1, v_interpreted_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 2, v_ctor_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 3, v_hasLambdas_3059_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 4, v_heqProofs_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 5, v_funCC_3065_);
v___x_3071_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3003_, v___x_3071_, v___y_2937_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_dec_ref_known(v___x_3072_, 1);
goto v___jp_2975_;
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_next_2956_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_fst_3003_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3084_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3048_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3048_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_fst_3003_);
lean_dec_ref(v_next_2956_);
lean_dec_ref(v_self_2955_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3092_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3046_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3046_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
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
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
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
v_a_3104_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3004_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3004_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
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
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
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
v_a_3112_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_2992_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_2992_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_del_object(v___x_2946_);
lean_dec(v_snd_2944_);
lean_dec_ref(v_rootNew_2934_);
v_a_3124_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_2950_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_2950_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3134_, lean_object* v_rootNew_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v_a_26841__boxed_3145_; lean_object* v_res_3146_; 
v_a_26841__boxed_3145_ = lean_unbox(v_a_3136_);
v_res_3146_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3134_, v_rootNew_3135_, v_a_26841__boxed_3145_, v_a_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v_lhs_3134_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3147_, lean_object* v_rootNew_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3148_, v_a_3153_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___x_3162_ = lean_box(0);
lean_inc_ref(v_lhs_3147_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
lean_ctor_set(v___x_3163_, 1, v_lhs_3147_);
v___x_3164_ = lean_unbox(v_a_3161_);
lean_dec(v_a_3161_);
v___x_3165_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3147_, v_rootNew_3148_, v___x_3164_, v___x_3163_, v_a_3149_, v_a_3153_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
lean_dec_ref(v_lhs_3147_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3179_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3168_ = v___x_3165_;
v_isShared_3169_ = v_isSharedCheck_3179_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3165_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3179_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_fst_3170_; 
v_fst_3170_ = lean_ctor_get(v_a_3166_, 0);
lean_inc(v_fst_3170_);
lean_dec(v_a_3166_);
if (lean_obj_tag(v_fst_3170_) == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(0);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3171_);
v___x_3173_ = v___x_3168_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
else
{
lean_object* v_val_3175_; lean_object* v___x_3177_; 
v_val_3175_ = lean_ctor_get(v_fst_3170_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v_fst_3170_, 1);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v_val_3175_);
v___x_3177_ = v___x_3168_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_val_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
v_a_3180_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3165_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3165_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec_ref(v_rootNew_3148_);
lean_dec_ref(v_lhs_3147_);
v_a_3188_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3160_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3160_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3196_, lean_object* v_rootNew_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3196_, v_rootNew_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec(v_a_3198_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3210_, lean_object* v_00_u03b2_3211_, lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3210_, v_x_3212_, v_x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3215_, lean_object* v_00_u03b2_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3215_, v_00_u03b2_3216_, v_x_3217_, v_x_3218_);
lean_dec_ref(v_x_3217_);
lean_dec_ref(v___x_3215_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3220_, lean_object* v_00_u03b2_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3220_, v_x_3222_, v_x_3223_, v_x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3226_, lean_object* v_00_u03b2_3227_, lean_object* v_x_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3226_, v_00_u03b2_3227_, v_x_3228_, v_x_3229_, v_x_3230_);
lean_dec_ref(v___x_3226_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3232_, lean_object* v_rootNew_3233_, uint8_t v_a_3234_, lean_object* v_inst_3235_, lean_object* v_a_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3232_, v_rootNew_3233_, v_a_3234_, v_a_3236_, v___y_3237_, v___y_3241_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3249_, lean_object* v_rootNew_3250_, lean_object* v_a_3251_, lean_object* v_inst_3252_, lean_object* v_a_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
uint8_t v_a_27226__boxed_3265_; lean_object* v_res_3266_; 
v_a_27226__boxed_3265_ = lean_unbox(v_a_3251_);
v_res_3266_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3249_, v_rootNew_3250_, v_a_27226__boxed_3265_, v_inst_3252_, v_a_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v_lhs_3249_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3267_, lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, size_t v_x_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; 
lean_inc_ref(v_x_3269_);
v___x_3272_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3267_, v_x_3269_, v_x_3270_, v_x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3273_, lean_object* v_00_u03b2_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_){
_start:
{
size_t v_x_27269__boxed_3278_; lean_object* v_res_3279_; 
v_x_27269__boxed_3278_ = lean_unbox_usize(v_x_3276_);
lean_dec(v_x_3276_);
v_res_3279_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3273_, v_00_u03b2_3274_, v_x_3275_, v_x_27269__boxed_3278_, v_x_3277_);
lean_dec_ref(v_x_3275_);
lean_dec_ref(v___x_3273_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3280_, lean_object* v_00_u03b2_3281_, lean_object* v_x_3282_, size_t v_x_3283_, size_t v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3280_, v_x_3282_, v_x_3283_, v_x_3284_, v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_, lean_object* v_x_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
size_t v_x_27283__boxed_3295_; size_t v_x_27284__boxed_3296_; lean_object* v_res_3297_; 
v_x_27283__boxed_3295_ = lean_unbox_usize(v_x_3291_);
lean_dec(v_x_3291_);
v_x_27284__boxed_3296_ = lean_unbox_usize(v_x_3292_);
lean_dec(v_x_3292_);
v_res_3297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3288_, v_00_u03b2_3289_, v_x_3290_, v_x_27283__boxed_3295_, v_x_27284__boxed_3296_, v_x_3293_, v_x_3294_);
lean_dec_ref(v___x_3288_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_keys_3300_, lean_object* v_vals_3301_, lean_object* v_heq_3302_, lean_object* v_i_3303_, lean_object* v_k_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3298_, v_keys_3300_, v_vals_3301_, v_i_3303_, v_k_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3306_, lean_object* v_00_u03b2_3307_, lean_object* v_keys_3308_, lean_object* v_vals_3309_, lean_object* v_heq_3310_, lean_object* v_i_3311_, lean_object* v_k_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3306_, v_00_u03b2_3307_, v_keys_3308_, v_vals_3309_, v_heq_3310_, v_i_3311_, v_k_3312_);
lean_dec_ref(v_vals_3309_);
lean_dec_ref(v_keys_3308_);
lean_dec_ref(v___x_3306_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3314_, lean_object* v_00_u03b2_3315_, lean_object* v_n_3316_, lean_object* v_k_3317_, lean_object* v_v_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3314_, v_n_3316_, v_k_3317_, v_v_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3320_, lean_object* v_00_u03b2_3321_, lean_object* v_n_3322_, lean_object* v_k_3323_, lean_object* v_v_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3320_, v_00_u03b2_3321_, v_n_3322_, v_k_3323_, v_v_3324_);
lean_dec_ref(v___x_3320_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3326_, lean_object* v_00_u03b2_3327_, size_t v_depth_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_entries_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3326_, v_depth_3328_, v_keys_3329_, v_vals_3330_, v_i_3332_, v_entries_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3335_, lean_object* v_00_u03b2_3336_, lean_object* v_depth_3337_, lean_object* v_keys_3338_, lean_object* v_vals_3339_, lean_object* v_heq_3340_, lean_object* v_i_3341_, lean_object* v_entries_3342_){
_start:
{
size_t v_depth_boxed_3343_; lean_object* v_res_3344_; 
v_depth_boxed_3343_ = lean_unbox_usize(v_depth_3337_);
lean_dec(v_depth_3337_);
v_res_3344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3335_, v_00_u03b2_3336_, v_depth_boxed_3343_, v_keys_3338_, v_vals_3339_, v_heq_3340_, v_i_3341_, v_entries_3342_);
lean_dec_ref(v_vals_3339_);
lean_dec_ref(v_keys_3338_);
lean_dec_ref(v___x_3335_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3345_, lean_object* v_00_u03b2_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3345_, v_x_3347_, v_x_3348_, v_x_3349_, v_x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3352_, lean_object* v_00_u03b2_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_, lean_object* v_x_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3352_, v_00_u03b2_3353_, v_x_3354_, v_x_3355_, v_x_3356_, v_x_3357_);
lean_dec_ref(v___x_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3359_, lean_object* v_b_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
if (lean_obj_tag(v_as_x27_3359_) == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_b_3360_);
return v___x_3372_;
}
else
{
lean_object* v_head_3373_; lean_object* v_tail_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_head_3373_ = lean_ctor_get(v_as_x27_3359_, 0);
v_tail_3374_ = lean_ctor_get(v_as_x27_3359_, 1);
v___x_3375_ = lean_box(0);
lean_inc(v_head_3373_);
v___x_3376_ = l_Lean_Meta_Grind_propagateUp(v_head_3373_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_dec_ref_known(v___x_3376_, 1);
v_as_x27_3359_ = v_tail_3374_;
v_b_3360_ = v___x_3375_;
goto _start;
}
else
{
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3378_, lean_object* v_b_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3378_, v_b_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v_as_x27_3378_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3392_, lean_object* v_b_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
if (lean_obj_tag(v_as_x27_3392_) == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3393_);
return v___x_3405_;
}
else
{
lean_object* v_head_3406_; lean_object* v_tail_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_head_3406_ = lean_ctor_get(v_as_x27_3392_, 0);
v_tail_3407_ = lean_ctor_get(v_as_x27_3392_, 1);
v___x_3408_ = lean_box(0);
lean_inc(v_head_3406_);
v___x_3409_ = l_Lean_Meta_Grind_propagateDown(v_head_3406_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_dec_ref_known(v___x_3409_, 1);
v_as_x27_3392_ = v_tail_3407_;
v_b_3393_ = v___x_3408_;
goto _start;
}
else
{
return v___x_3409_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3411_, v_b_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec(v_as_x27_3411_);
return v_res_3424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_cls_3428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3429_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3430_ = l_Lean_Name_append(v___x_3429_, v_cls_3428_);
return v___x_3430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3443_, uint8_t v_isHEq_3444_, lean_object* v_lhs_3445_, lean_object* v_rhs_3446_, lean_object* v_lhsNode_3447_, lean_object* v_rhsNode_3448_, lean_object* v_lhsRoot_3449_, lean_object* v_rhsRoot_3450_, uint8_t v_flipped_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; uint8_t v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3604_; uint8_t v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v_toCold_3709_; lean_object* v_options_3710_; lean_object* v_inheritedTraceOptions_3711_; uint8_t v_hasTrace_3712_; lean_object* v_cls_3713_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v_fns_u2082_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v_fns_u2081_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; 
v_toCold_3709_ = lean_ctor_get(v_a_3460_, 0);
v_options_3710_ = lean_ctor_get(v_toCold_3709_, 2);
v_inheritedTraceOptions_3711_ = lean_ctor_get(v_toCold_3709_, 11);
v_hasTrace_3712_ = lean_ctor_get_uint8(v_options_3710_, sizeof(void*)*1);
v_cls_3713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3712_ == 0)
{
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
goto v___jp_3832_;
}
else
{
lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3711_, v_options_3710_, v___x_3913_);
if (v___x_3914_ == 0)
{
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
goto v___jp_3832_;
}
else
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Meta_Grind_updateLastTag(v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref_known(v___x_3915_, 1);
lean_inc_ref(v_lhs_3445_);
v___x_3916_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3445_, v_a_3452_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
lean_inc_ref(v_rhs_3446_);
v___x_3918_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3446_, v_a_3452_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3920_);
lean_ctor_set(v___x_3921_, 1, v_a_3917_);
v___x_3922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_a_3919_);
v___x_3925_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3713_, v___x_3924_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_dec_ref_known(v___x_3925_, 1);
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
goto v___jp_3832_;
}
else
{
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhsNode_3447_);
lean_dec_ref(v_rhs_3446_);
lean_dec_ref(v_lhs_3445_);
lean_dec_ref(v_proof_3443_);
return v___x_3925_;
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3917_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhsNode_3447_);
lean_dec_ref(v_rhs_3446_);
lean_dec_ref(v_lhs_3445_);
lean_dec_ref(v_proof_3443_);
v_a_3926_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3918_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3918_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhsNode_3447_);
lean_dec_ref(v_rhs_3446_);
lean_dec_ref(v_lhs_3445_);
lean_dec_ref(v_proof_3443_);
v_a_3934_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3916_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3916_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhsNode_3447_);
lean_dec_ref(v_rhs_3446_);
lean_dec_ref(v_lhs_3445_);
lean_dec_ref(v_proof_3443_);
return v___x_3915_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3470_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3506_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3506_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3506_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_unbox(v_a_3481_);
lean_dec(v_a_3481_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_del_object(v___x_3483_);
v___x_3486_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3465_);
lean_dec(v___y_3465_);
v___x_3487_ = lean_box(0);
v___x_3488_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3486_, v___x_3487_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___x_3486_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref_known(v___x_3488_, 1);
v___x_3489_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3466_, v___x_3487_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v___x_3490_; 
lean_dec_ref_known(v___x_3489_, 1);
v___x_3490_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3464_, v___y_3468_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3464_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
lean_dec_ref_known(v___x_3490_, 1);
v___x_3491_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3467_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3491_, 0);
lean_dec(v_unused_3501_);
v___x_3493_ = v___x_3491_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v___x_3491_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
uint8_t v___x_3495_; 
v___x_3495_ = l_Lean_Expr_isTrue(v___y_3469_);
lean_dec_ref(v___y_3469_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3497_; 
lean_dec(v___y_3466_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3487_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3487_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
lean_object* v___x_3499_; 
lean_del_object(v___x_3493_);
v___x_3499_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3466_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3466_);
return v___x_3499_;
}
}
}
else
{
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3466_);
return v___x_3491_;
}
}
else
{
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
return v___x_3490_;
}
}
else
{
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3464_);
return v___x_3489_;
}
}
else
{
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3464_);
return v___x_3488_;
}
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
v___x_3502_ = lean_box(0);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3502_);
v___x_3504_ = v___x_3483_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
v_a_3507_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3480_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3480_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
v___jp_3515_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_inc_ref(v___y_3516_);
v___x_3553_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3553_, 0, v___y_3516_);
lean_ctor_set(v___x_3553_, 1, v___y_3544_);
lean_ctor_set(v___x_3553_, 2, v___y_3523_);
lean_ctor_set(v___x_3553_, 3, v___y_3536_);
lean_ctor_set(v___x_3553_, 4, v___y_3540_);
lean_ctor_set(v___x_3553_, 5, v___y_3521_);
lean_ctor_set(v___x_3553_, 6, v___y_3519_);
lean_ctor_set(v___x_3553_, 7, v___y_3529_);
lean_ctor_set(v___x_3553_, 8, v___y_3539_);
lean_ctor_set(v___x_3553_, 9, v___y_3543_);
lean_ctor_set(v___x_3553_, 10, v___y_3551_);
lean_ctor_set(v___x_3553_, 11, v___y_3518_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12, v___y_3520_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12 + 1, v___y_3538_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12 + 2, v___y_3549_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12 + 3, v___y_3552_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12 + 4, v___y_3524_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*12 + 5, v___y_3545_);
lean_inc_ref(v___y_3534_);
v___x_3554_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3534_, v___x_3553_, v___y_3547_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v___x_3555_; 
lean_dec_ref_known(v___x_3554_, 1);
lean_inc_ref(v___y_3528_);
v___x_3555_ = l_Lean_Meta_Grind_propagateBeta(v___y_3528_, v___y_3517_, v___y_3547_, v___y_3530_, v___y_3532_, v___y_3550_, v___y_3546_, v___y_3526_, v___y_3527_, v___y_3541_, v___y_3542_, v___y_3535_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v___x_3556_; 
lean_dec_ref_known(v___x_3555_, 1);
lean_inc_ref(v___y_3533_);
v___x_3556_ = l_Lean_Meta_Grind_propagateBeta(v___y_3533_, v___y_3531_, v___y_3547_, v___y_3530_, v___y_3532_, v___y_3550_, v___y_3546_, v___y_3526_, v___y_3527_, v___y_3541_, v___y_3542_, v___y_3535_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref_known(v___x_3556_, 1);
v___x_3557_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v___y_3548_, v_lhsRoot_3449_, v___y_3524_, v___y_3547_, v___y_3527_, v___y_3541_, v___y_3542_, v___y_3535_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3525_, v___y_3547_);
lean_dec_ref(v___y_3525_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v___x_3560_; 
lean_dec_ref_known(v___x_3559_, 1);
lean_inc_ref(v___y_3534_);
v___x_3560_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3537_, v___y_3534_, v___y_3547_, v___y_3530_, v___y_3532_, v___y_3550_, v___y_3546_, v___y_3526_, v___y_3527_, v___y_3541_, v___y_3542_, v___y_3535_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3561_; 
lean_dec_ref_known(v___x_3560_, 1);
v___x_3561_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3547_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; uint8_t v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = lean_unbox(v_a_3562_);
lean_dec(v_a_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3516_, v___y_3547_, v___y_3530_, v___y_3532_, v___y_3550_, v___y_3546_, v___y_3526_, v___y_3527_, v___y_3541_, v___y_3542_, v___y_3535_);
lean_dec_ref(v___y_3516_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_dec_ref_known(v___x_3564_, 1);
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3537_;
v___y_3466_ = v___y_3522_;
v___y_3467_ = v_a_3558_;
v___y_3468_ = v___y_3533_;
v___y_3469_ = v___y_3534_;
v___y_3470_ = v___y_3547_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3532_;
v___y_3473_ = v___y_3550_;
v___y_3474_ = v___y_3546_;
v___y_3475_ = v___y_3526_;
v___y_3476_ = v___y_3527_;
v___y_3477_ = v___y_3541_;
v___y_3478_ = v___y_3542_;
v___y_3479_ = v___y_3535_;
goto v___jp_3463_;
}
else
{
lean_dec(v_a_3558_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3522_);
return v___x_3564_;
}
}
else
{
lean_dec_ref(v___y_3516_);
v___y_3464_ = v___y_3528_;
v___y_3465_ = v___y_3537_;
v___y_3466_ = v___y_3522_;
v___y_3467_ = v_a_3558_;
v___y_3468_ = v___y_3533_;
v___y_3469_ = v___y_3534_;
v___y_3470_ = v___y_3547_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3532_;
v___y_3473_ = v___y_3550_;
v___y_3474_ = v___y_3546_;
v___y_3475_ = v___y_3526_;
v___y_3476_ = v___y_3527_;
v___y_3477_ = v___y_3541_;
v___y_3478_ = v___y_3542_;
v___y_3479_ = v___y_3535_;
goto v___jp_3463_;
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v_a_3558_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
v_a_3565_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3561_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3561_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_dec(v_a_3558_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
return v___x_3560_;
}
}
else
{
lean_dec(v_a_3558_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
return v___x_3559_;
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
v_a_3573_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3557_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3557_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_lhsRoot_3449_);
return v___x_3556_;
}
}
else
{
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_lhsRoot_3449_);
return v___x_3555_;
}
}
else
{
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_lhsRoot_3449_);
return v___x_3554_;
}
}
v___jp_3581_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_st_ref_get(v___y_3597_);
v___x_3606_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3605_, v___y_3603_, v___y_3589_, v___y_3585_, v___y_3587_, v___y_3601_);
lean_dec(v___x_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v_self_3608_; lean_object* v_root_3609_; lean_object* v_congr_3610_; lean_object* v_target_x3f_3611_; lean_object* v_proof_x3f_3612_; uint8_t v_flipped_3613_; lean_object* v_size_3614_; uint8_t v_interpreted_3615_; uint8_t v_ctor_3616_; uint8_t v_hasLambdas_3617_; lean_object* v_idx_3618_; lean_object* v_generation_3619_; lean_object* v_mt_3620_; lean_object* v_sTerms_3621_; uint8_t v_funCC_3622_; lean_object* v_ematchDiagSource_3623_; lean_object* v___x_3624_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v_self_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc_ref(v_self_3608_);
v_root_3609_ = lean_ctor_get(v_a_3607_, 2);
lean_inc_ref(v_root_3609_);
v_congr_3610_ = lean_ctor_get(v_a_3607_, 3);
lean_inc_ref(v_congr_3610_);
v_target_x3f_3611_ = lean_ctor_get(v_a_3607_, 4);
lean_inc(v_target_x3f_3611_);
v_proof_x3f_3612_ = lean_ctor_get(v_a_3607_, 5);
lean_inc(v_proof_x3f_3612_);
v_flipped_3613_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*12);
v_size_3614_ = lean_ctor_get(v_a_3607_, 6);
v_interpreted_3615_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*12 + 1);
v_ctor_3616_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*12 + 2);
v_hasLambdas_3617_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*12 + 3);
v_idx_3618_ = lean_ctor_get(v_a_3607_, 7);
lean_inc(v_idx_3618_);
v_generation_3619_ = lean_ctor_get(v_a_3607_, 8);
lean_inc(v_generation_3619_);
v_mt_3620_ = lean_ctor_get(v_a_3607_, 9);
lean_inc(v_mt_3620_);
v_sTerms_3621_ = lean_ctor_get(v_a_3607_, 10);
lean_inc(v_sTerms_3621_);
v_funCC_3622_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3623_ = lean_ctor_get(v_a_3607_, 11);
lean_inc(v_ematchDiagSource_3623_);
v___x_3624_ = lean_nat_add(v_size_3614_, v___y_3602_);
lean_dec(v___y_3602_);
if (v_hasLambdas_3617_ == 0)
{
v___y_3516_ = v_self_3608_;
v___y_3517_ = v___y_3582_;
v___y_3518_ = v_ematchDiagSource_3623_;
v___y_3519_ = v___x_3624_;
v___y_3520_ = v_flipped_3613_;
v___y_3521_ = v_proof_x3f_3612_;
v___y_3522_ = v___y_3584_;
v___y_3523_ = v_root_3609_;
v___y_3524_ = v___y_3604_;
v___y_3525_ = v___y_3586_;
v___y_3526_ = v___y_3588_;
v___y_3527_ = v___y_3589_;
v___y_3528_ = v___y_3590_;
v___y_3529_ = v_idx_3618_;
v___y_3530_ = v___y_3594_;
v___y_3531_ = v___y_3596_;
v___y_3532_ = v___y_3595_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v_congr_3610_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v_interpreted_3615_;
v___y_3539_ = v_generation_3619_;
v___y_3540_ = v_target_x3f_3611_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v_mt_3620_;
v___y_3544_ = v___y_3591_;
v___y_3545_ = v_funCC_3622_;
v___y_3546_ = v___y_3593_;
v___y_3547_ = v___y_3597_;
v___y_3548_ = v_a_3607_;
v___y_3549_ = v_ctor_3616_;
v___y_3550_ = v___y_3598_;
v___y_3551_ = v_sTerms_3621_;
v___y_3552_ = v___y_3592_;
goto v___jp_3515_;
}
else
{
v___y_3516_ = v_self_3608_;
v___y_3517_ = v___y_3582_;
v___y_3518_ = v_ematchDiagSource_3623_;
v___y_3519_ = v___x_3624_;
v___y_3520_ = v_flipped_3613_;
v___y_3521_ = v_proof_x3f_3612_;
v___y_3522_ = v___y_3584_;
v___y_3523_ = v_root_3609_;
v___y_3524_ = v___y_3604_;
v___y_3525_ = v___y_3586_;
v___y_3526_ = v___y_3588_;
v___y_3527_ = v___y_3589_;
v___y_3528_ = v___y_3590_;
v___y_3529_ = v_idx_3618_;
v___y_3530_ = v___y_3594_;
v___y_3531_ = v___y_3596_;
v___y_3532_ = v___y_3595_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3601_;
v___y_3536_ = v_congr_3610_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v_interpreted_3615_;
v___y_3539_ = v_generation_3619_;
v___y_3540_ = v_target_x3f_3611_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v_mt_3620_;
v___y_3544_ = v___y_3591_;
v___y_3545_ = v_funCC_3622_;
v___y_3546_ = v___y_3593_;
v___y_3547_ = v___y_3597_;
v___y_3548_ = v_a_3607_;
v___y_3549_ = v_ctor_3616_;
v___y_3550_ = v___y_3598_;
v___y_3551_ = v_sTerms_3621_;
v___y_3552_ = v_hasLambdas_3617_;
goto v___jp_3515_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v_lhsRoot_3449_);
v_a_3625_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3606_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3606_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
v___jp_3633_:
{
lean_object* v___x_3656_; 
v___x_3656_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3639_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3656_) == 0)
{
uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec_ref_known(v___x_3656_, 1);
v___x_3657_ = 0;
v___x_3658_ = lean_st_ref_get(v___y_3646_);
v___x_3659_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3658_, v_lhs_3445_, v___x_3657_);
lean_dec(v___x_3658_);
v___x_3660_ = lean_st_ref_get(v___y_3646_);
lean_inc_ref(v___y_3644_);
v___x_3661_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3660_, v___y_3644_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___x_3660_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v_self_3663_; lean_object* v_root_3664_; lean_object* v_congr_3665_; lean_object* v_target_x3f_3666_; lean_object* v_proof_x3f_3667_; uint8_t v_flipped_3668_; lean_object* v_size_3669_; uint8_t v_interpreted_3670_; uint8_t v_ctor_3671_; uint8_t v_hasLambdas_3672_; uint8_t v_heqProofs_3673_; lean_object* v_idx_3674_; lean_object* v_generation_3675_; lean_object* v_mt_3676_; lean_object* v_sTerms_3677_; uint8_t v_funCC_3678_; lean_object* v_ematchDiagSource_3679_; lean_object* v_self_3680_; lean_object* v_next_3681_; uint8_t v_heqProofs_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3690_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v_self_3663_ = lean_ctor_get(v_a_3662_, 0);
lean_inc_ref(v_self_3663_);
v_root_3664_ = lean_ctor_get(v_a_3662_, 2);
lean_inc_ref(v_root_3664_);
v_congr_3665_ = lean_ctor_get(v_a_3662_, 3);
lean_inc_ref(v_congr_3665_);
v_target_x3f_3666_ = lean_ctor_get(v_a_3662_, 4);
lean_inc(v_target_x3f_3666_);
v_proof_x3f_3667_ = lean_ctor_get(v_a_3662_, 5);
lean_inc(v_proof_x3f_3667_);
v_flipped_3668_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12);
v_size_3669_ = lean_ctor_get(v_a_3662_, 6);
lean_inc(v_size_3669_);
v_interpreted_3670_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12 + 1);
v_ctor_3671_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12 + 2);
v_hasLambdas_3672_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12 + 3);
v_heqProofs_3673_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12 + 4);
v_idx_3674_ = lean_ctor_get(v_a_3662_, 7);
lean_inc(v_idx_3674_);
v_generation_3675_ = lean_ctor_get(v_a_3662_, 8);
lean_inc(v_generation_3675_);
v_mt_3676_ = lean_ctor_get(v_a_3662_, 9);
lean_inc(v_mt_3676_);
v_sTerms_3677_ = lean_ctor_get(v_a_3662_, 10);
lean_inc(v_sTerms_3677_);
v_funCC_3678_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3679_ = lean_ctor_get(v_a_3662_, 11);
lean_inc(v_ematchDiagSource_3679_);
lean_dec(v_a_3662_);
v_self_3680_ = lean_ctor_get(v_rhsRoot_3450_, 0);
v_next_3681_ = lean_ctor_get(v_rhsRoot_3450_, 1);
v_heqProofs_3682_ = lean_ctor_get_uint8(v_rhsRoot_3450_, sizeof(void*)*12 + 4);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_rhsRoot_3450_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3691_ = lean_ctor_get(v_rhsRoot_3450_, 11);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_rhsRoot_3450_, 10);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_rhsRoot_3450_, 9);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_rhsRoot_3450_, 8);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_rhsRoot_3450_, 7);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_rhsRoot_3450_, 6);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_rhsRoot_3450_, 5);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_rhsRoot_3450_, 4);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_rhsRoot_3450_, 3);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_rhsRoot_3450_, 2);
lean_dec(v_unused_3700_);
v___x_3684_ = v_rhsRoot_3450_;
v_isShared_3685_ = v_isSharedCheck_3690_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_next_3681_);
lean_inc(v_self_3680_);
lean_dec(v_rhsRoot_3450_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3690_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 11, v_ematchDiagSource_3679_);
lean_ctor_set(v___x_3684_, 10, v_sTerms_3677_);
lean_ctor_set(v___x_3684_, 9, v_mt_3676_);
lean_ctor_set(v___x_3684_, 8, v_generation_3675_);
lean_ctor_set(v___x_3684_, 7, v_idx_3674_);
lean_ctor_set(v___x_3684_, 6, v_size_3669_);
lean_ctor_set(v___x_3684_, 5, v_proof_x3f_3667_);
lean_ctor_set(v___x_3684_, 4, v_target_x3f_3666_);
lean_ctor_set(v___x_3684_, 3, v_congr_3665_);
lean_ctor_set(v___x_3684_, 2, v_root_3664_);
lean_ctor_set(v___x_3684_, 0, v_self_3663_);
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_self_3663_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_next_3681_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_root_3664_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_congr_3665_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v_target_x3f_3666_);
lean_ctor_set(v_reuseFailAlloc_3689_, 5, v_proof_x3f_3667_);
lean_ctor_set(v_reuseFailAlloc_3689_, 6, v_size_3669_);
lean_ctor_set(v_reuseFailAlloc_3689_, 7, v_idx_3674_);
lean_ctor_set(v_reuseFailAlloc_3689_, 8, v_generation_3675_);
lean_ctor_set(v_reuseFailAlloc_3689_, 9, v_mt_3676_);
lean_ctor_set(v_reuseFailAlloc_3689_, 10, v_sTerms_3677_);
lean_ctor_set(v_reuseFailAlloc_3689_, 11, v_ematchDiagSource_3679_);
v___x_3687_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3688_; 
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12, v_flipped_3668_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12 + 1, v_interpreted_3670_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12 + 2, v_ctor_3671_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12 + 3, v_hasLambdas_3672_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12 + 4, v_heqProofs_3673_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*12 + 5, v_funCC_3678_);
v___x_3688_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3637_, v___x_3687_, v___y_3646_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_dec_ref_known(v___x_3688_, 1);
if (v_isHEq_3444_ == 0)
{
if (v_heqProofs_3682_ == 0)
{
v___y_3582_ = v___y_3636_;
v___y_3583_ = v___y_3639_;
v___y_3584_ = v___x_3659_;
v___y_3585_ = v___y_3653_;
v___y_3586_ = v___y_3644_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3651_;
v___y_3589_ = v___y_3652_;
v___y_3590_ = v___y_3635_;
v___y_3591_ = v___y_3638_;
v___y_3592_ = v___y_3640_;
v___y_3593_ = v___y_3650_;
v___y_3594_ = v___y_3647_;
v___y_3595_ = v___y_3648_;
v___y_3596_ = v___y_3641_;
v___y_3597_ = v___y_3646_;
v___y_3598_ = v___y_3649_;
v___y_3599_ = v___y_3642_;
v___y_3600_ = v___y_3643_;
v___y_3601_ = v___y_3655_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v_self_3680_;
v___y_3604_ = v___y_3634_;
goto v___jp_3581_;
}
else
{
v___y_3582_ = v___y_3636_;
v___y_3583_ = v___y_3639_;
v___y_3584_ = v___x_3659_;
v___y_3585_ = v___y_3653_;
v___y_3586_ = v___y_3644_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3651_;
v___y_3589_ = v___y_3652_;
v___y_3590_ = v___y_3635_;
v___y_3591_ = v___y_3638_;
v___y_3592_ = v___y_3640_;
v___y_3593_ = v___y_3650_;
v___y_3594_ = v___y_3647_;
v___y_3595_ = v___y_3648_;
v___y_3596_ = v___y_3641_;
v___y_3597_ = v___y_3646_;
v___y_3598_ = v___y_3649_;
v___y_3599_ = v___y_3642_;
v___y_3600_ = v___y_3643_;
v___y_3601_ = v___y_3655_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v_self_3680_;
v___y_3604_ = v_heqProofs_3682_;
goto v___jp_3581_;
}
}
else
{
v___y_3582_ = v___y_3636_;
v___y_3583_ = v___y_3639_;
v___y_3584_ = v___x_3659_;
v___y_3585_ = v___y_3653_;
v___y_3586_ = v___y_3644_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3651_;
v___y_3589_ = v___y_3652_;
v___y_3590_ = v___y_3635_;
v___y_3591_ = v___y_3638_;
v___y_3592_ = v___y_3640_;
v___y_3593_ = v___y_3650_;
v___y_3594_ = v___y_3647_;
v___y_3595_ = v___y_3648_;
v___y_3596_ = v___y_3641_;
v___y_3597_ = v___y_3646_;
v___y_3598_ = v___y_3649_;
v___y_3599_ = v___y_3642_;
v___y_3600_ = v___y_3643_;
v___y_3601_ = v___y_3655_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v_self_3680_;
v___y_3604_ = v_isHEq_3444_;
goto v___jp_3581_;
}
}
else
{
lean_dec_ref(v_self_3680_);
lean_dec(v___x_3659_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_lhsRoot_3449_);
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v___x_3659_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
v_a_3701_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3661_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3661_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
return v___x_3656_;
}
}
v___jp_3714_:
{
lean_object* v_self_3730_; lean_object* v_next_3731_; lean_object* v_size_3732_; uint8_t v_hasLambdas_3733_; uint8_t v_heqProofs_3734_; lean_object* v___x_3735_; 
v_self_3730_ = lean_ctor_get(v_lhsRoot_3449_, 0);
v_next_3731_ = lean_ctor_get(v_lhsRoot_3449_, 1);
v_size_3732_ = lean_ctor_get(v_lhsRoot_3449_, 6);
v_hasLambdas_3733_ = lean_ctor_get_uint8(v_lhsRoot_3449_, sizeof(void*)*12 + 3);
v_heqProofs_3734_ = lean_ctor_get_uint8(v_lhsRoot_3449_, sizeof(void*)*12 + 4);
v___x_3735_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3730_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v_root_3737_; lean_object* v___x_3738_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v_root_3737_ = lean_ctor_get(v_rhsNode_3448_, 2);
lean_inc_ref_n(v_root_3737_, 2);
lean_dec_ref(v_rhsNode_3448_);
lean_inc_ref(v_lhs_3445_);
v___x_3738_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3445_, v_root_3737_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_toCold_3739_; lean_object* v_options_3740_; uint8_t v_hasTrace_3741_; 
lean_dec_ref_known(v___x_3738_, 1);
v_toCold_3739_ = lean_ctor_get(v___y_3728_, 0);
v_options_3740_ = lean_ctor_get(v_toCold_3739_, 2);
v_hasTrace_3741_ = lean_ctor_get_uint8(v_options_3740_, sizeof(void*)*1);
if (v_hasTrace_3741_ == 0)
{
lean_inc(v_size_3732_);
lean_inc_ref(v_self_3730_);
lean_inc_ref(v_next_3731_);
v___y_3634_ = v_heqProofs_3734_;
v___y_3635_ = v___y_3717_;
v___y_3636_ = v___y_3716_;
v___y_3637_ = v___y_3715_;
v___y_3638_ = v_next_3731_;
v___y_3639_ = v_a_3736_;
v___y_3640_ = v_hasLambdas_3733_;
v___y_3641_ = v_fns_u2082_3719_;
v___y_3642_ = v___y_3718_;
v___y_3643_ = v_root_3737_;
v___y_3644_ = v_self_3730_;
v___y_3645_ = v_size_3732_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
goto v___jp_3633_;
}
else
{
lean_object* v_inheritedTraceOptions_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_inheritedTraceOptions_3742_ = lean_ctor_get(v_toCold_3739_, 11);
v___x_3743_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3742_, v_options_3740_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_inc(v_size_3732_);
lean_inc_ref(v_self_3730_);
lean_inc_ref(v_next_3731_);
v___y_3634_ = v_heqProofs_3734_;
v___y_3635_ = v___y_3717_;
v___y_3636_ = v___y_3716_;
v___y_3637_ = v___y_3715_;
v___y_3638_ = v_next_3731_;
v___y_3639_ = v_a_3736_;
v___y_3640_ = v_hasLambdas_3733_;
v___y_3641_ = v_fns_u2082_3719_;
v___y_3642_ = v___y_3718_;
v___y_3643_ = v_root_3737_;
v___y_3644_ = v_self_3730_;
v___y_3645_ = v_size_3732_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
goto v___jp_3633_;
}
else
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_Grind_updateLastTag(v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v___x_3746_; 
lean_dec_ref_known(v___x_3745_, 1);
lean_inc_ref(v_lhs_3445_);
v___x_3746_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3445_, v___y_3720_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
lean_inc_ref(v_root_3737_);
v___x_3748_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3737_, v___y_3720_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3750_ = lean_st_ref_get(v___y_3720_);
lean_inc_ref(v_lhs_3445_);
v___x_3751_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3750_, v_lhs_3445_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___x_3750_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3753_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3752_, v___y_3720_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v___x_3755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v_a_3747_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v_a_3749_);
v___x_3758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v_a_3754_);
v___x_3761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3713_, v___x_3760_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_dec_ref_known(v___x_3761_, 1);
lean_inc(v_size_3732_);
lean_inc_ref(v_self_3730_);
lean_inc_ref(v_next_3731_);
v___y_3634_ = v_heqProofs_3734_;
v___y_3635_ = v___y_3717_;
v___y_3636_ = v___y_3716_;
v___y_3637_ = v___y_3715_;
v___y_3638_ = v_next_3731_;
v___y_3639_ = v_a_3736_;
v___y_3640_ = v_hasLambdas_3733_;
v___y_3641_ = v_fns_u2082_3719_;
v___y_3642_ = v___y_3718_;
v___y_3643_ = v_root_3737_;
v___y_3644_ = v_self_3730_;
v___y_3645_ = v_size_3732_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
goto v___jp_3633_;
}
else
{
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
return v___x_3761_;
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_a_3749_);
lean_dec(v_a_3747_);
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
v_a_3762_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3753_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3753_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_a_3749_);
lean_dec(v_a_3747_);
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
v_a_3770_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3751_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3751_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec(v_a_3747_);
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
v_a_3778_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3748_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3748_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
v_a_3786_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3746_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3746_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
return v___x_3745_;
}
}
}
}
else
{
lean_dec_ref(v_root_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_lhs_3445_);
return v___x_3738_;
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_fns_u2082_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
v_a_3794_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3735_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3735_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
v___jp_3802_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3817_ = lean_array_get_size(v___y_3805_);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_nat_dec_eq(v___x_3817_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_object* v_self_3820_; lean_object* v___x_3821_; 
v_self_3820_ = lean_ctor_get(v_lhsRoot_3449_, 0);
lean_inc_ref(v_self_3820_);
v___x_3821_ = l_Lean_Meta_Grind_getFnRoots(v_self_3820_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___y_3715_ = v___y_3804_;
v___y_3716_ = v_fns_u2081_3806_;
v___y_3717_ = v___y_3803_;
v___y_3718_ = v___y_3805_;
v_fns_u2082_3719_ = v_a_3822_;
v___y_3720_ = v___y_3807_;
v___y_3721_ = v___y_3808_;
v___y_3722_ = v___y_3809_;
v___y_3723_ = v___y_3810_;
v___y_3724_ = v___y_3811_;
v___y_3725_ = v___y_3812_;
v___y_3726_ = v___y_3813_;
v___y_3727_ = v___y_3814_;
v___y_3728_ = v___y_3815_;
v___y_3729_ = v___y_3816_;
goto v___jp_3714_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v_fns_u2081_3806_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
v_a_3823_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3821_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3821_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v___x_3831_; 
v___x_3831_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3715_ = v___y_3804_;
v___y_3716_ = v_fns_u2081_3806_;
v___y_3717_ = v___y_3803_;
v___y_3718_ = v___y_3805_;
v_fns_u2082_3719_ = v___x_3831_;
v___y_3720_ = v___y_3807_;
v___y_3721_ = v___y_3808_;
v___y_3722_ = v___y_3809_;
v___y_3723_ = v___y_3810_;
v___y_3724_ = v___y_3811_;
v___y_3725_ = v___y_3812_;
v___y_3726_ = v___y_3813_;
v___y_3727_ = v___y_3814_;
v___y_3728_ = v___y_3815_;
v___y_3729_ = v___y_3816_;
goto v___jp_3714_;
}
}
v___jp_3832_:
{
lean_object* v___x_3843_; 
lean_inc_ref(v_lhs_3445_);
v___x_3843_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3445_, v___y_3833_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v___x_3843_, 0);
lean_dec(v_unused_3912_);
v___x_3845_ = v___x_3843_;
v_isShared_3846_ = v_isSharedCheck_3911_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v___x_3843_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3911_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_self_3847_; lean_object* v_next_3848_; lean_object* v_root_3849_; lean_object* v_congr_3850_; lean_object* v_size_3851_; uint8_t v_interpreted_3852_; uint8_t v_ctor_3853_; uint8_t v_hasLambdas_3854_; uint8_t v_heqProofs_3855_; lean_object* v_idx_3856_; lean_object* v_generation_3857_; lean_object* v_mt_3858_; lean_object* v_sTerms_3859_; uint8_t v_funCC_3860_; lean_object* v_ematchDiagSource_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3908_; 
v_self_3847_ = lean_ctor_get(v_lhsNode_3447_, 0);
v_next_3848_ = lean_ctor_get(v_lhsNode_3447_, 1);
v_root_3849_ = lean_ctor_get(v_lhsNode_3447_, 2);
v_congr_3850_ = lean_ctor_get(v_lhsNode_3447_, 3);
v_size_3851_ = lean_ctor_get(v_lhsNode_3447_, 6);
v_interpreted_3852_ = lean_ctor_get_uint8(v_lhsNode_3447_, sizeof(void*)*12 + 1);
v_ctor_3853_ = lean_ctor_get_uint8(v_lhsNode_3447_, sizeof(void*)*12 + 2);
v_hasLambdas_3854_ = lean_ctor_get_uint8(v_lhsNode_3447_, sizeof(void*)*12 + 3);
v_heqProofs_3855_ = lean_ctor_get_uint8(v_lhsNode_3447_, sizeof(void*)*12 + 4);
v_idx_3856_ = lean_ctor_get(v_lhsNode_3447_, 7);
v_generation_3857_ = lean_ctor_get(v_lhsNode_3447_, 8);
v_mt_3858_ = lean_ctor_get(v_lhsNode_3447_, 9);
v_sTerms_3859_ = lean_ctor_get(v_lhsNode_3447_, 10);
v_funCC_3860_ = lean_ctor_get_uint8(v_lhsNode_3447_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3861_ = lean_ctor_get(v_lhsNode_3447_, 11);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_lhsNode_3447_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; lean_object* v_unused_3910_; 
v_unused_3909_ = lean_ctor_get(v_lhsNode_3447_, 5);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_lhsNode_3447_, 4);
lean_dec(v_unused_3910_);
v___x_3863_ = v_lhsNode_3447_;
v_isShared_3864_ = v_isSharedCheck_3908_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_ematchDiagSource_3861_);
lean_inc(v_sTerms_3859_);
lean_inc(v_mt_3858_);
lean_inc(v_generation_3857_);
lean_inc(v_idx_3856_);
lean_inc(v_size_3851_);
lean_inc(v_congr_3850_);
lean_inc(v_root_3849_);
lean_inc(v_next_3848_);
lean_inc(v_self_3847_);
lean_dec(v_lhsNode_3447_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3908_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 1);
lean_ctor_set(v___x_3845_, 0, v_rhs_3446_);
v___x_3866_ = v___x_3845_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_rhs_3446_);
v___x_3866_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3867_, 0, v_proof_3443_);
lean_inc_ref(v_root_3849_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 5, v___x_3867_);
lean_ctor_set(v___x_3863_, 4, v___x_3866_);
v___x_3869_ = v___x_3863_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_self_3847_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_next_3848_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_root_3849_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_congr_3850_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3906_, 5, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3906_, 6, v_size_3851_);
lean_ctor_set(v_reuseFailAlloc_3906_, 7, v_idx_3856_);
lean_ctor_set(v_reuseFailAlloc_3906_, 8, v_generation_3857_);
lean_ctor_set(v_reuseFailAlloc_3906_, 9, v_mt_3858_);
lean_ctor_set(v_reuseFailAlloc_3906_, 10, v_sTerms_3859_);
lean_ctor_set(v_reuseFailAlloc_3906_, 11, v_ematchDiagSource_3861_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*12 + 1, v_interpreted_3852_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*12 + 2, v_ctor_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*12 + 3, v_hasLambdas_3854_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*12 + 4, v_heqProofs_3855_);
lean_ctor_set_uint8(v_reuseFailAlloc_3906_, sizeof(void*)*12 + 5, v_funCC_3860_);
v___x_3869_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; 
lean_ctor_set_uint8(v___x_3869_, sizeof(void*)*12, v_flipped_3451_);
lean_inc_ref(v_lhs_3445_);
v___x_3870_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3445_, v___x_3869_, v___y_3833_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3871_; 
lean_dec_ref_known(v___x_3870_, 1);
v___x_3871_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3449_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
v___x_3873_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3450_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = lean_array_get_size(v_a_3872_);
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = lean_nat_dec_eq(v___x_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v_self_3878_; lean_object* v___x_3879_; 
v_self_3878_ = lean_ctor_get(v_rhsRoot_3450_, 0);
lean_inc_ref(v_self_3878_);
v___x_3879_ = l_Lean_Meta_Grind_getFnRoots(v_self_3878_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___y_3803_ = v_a_3872_;
v___y_3804_ = v_root_3849_;
v___y_3805_ = v_a_3874_;
v_fns_u2081_3806_ = v_a_3880_;
v___y_3807_ = v___y_3833_;
v___y_3808_ = v___y_3834_;
v___y_3809_ = v___y_3835_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___y_3839_;
v___y_3814_ = v___y_3840_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3842_;
goto v___jp_3802_;
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3874_);
lean_dec(v_a_3872_);
lean_dec_ref(v_root_3849_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
v_a_3881_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3879_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3879_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3803_ = v_a_3872_;
v___y_3804_ = v_root_3849_;
v___y_3805_ = v_a_3874_;
v_fns_u2081_3806_ = v___x_3889_;
v___y_3807_ = v___y_3833_;
v___y_3808_ = v___y_3834_;
v___y_3809_ = v___y_3835_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___y_3839_;
v___y_3814_ = v___y_3840_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3842_;
goto v___jp_3802_;
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_root_3849_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
v_a_3890_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3873_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3873_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec_ref(v_root_3849_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
v_a_3898_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3871_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3871_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_dec_ref(v_root_3849_);
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhs_3445_);
return v___x_3870_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3450_);
lean_dec_ref(v_lhsRoot_3449_);
lean_dec_ref(v_rhsNode_3448_);
lean_dec_ref(v_lhsNode_3447_);
lean_dec_ref(v_rhs_3446_);
lean_dec_ref(v_lhs_3445_);
lean_dec_ref(v_proof_3443_);
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3942_ = _args[0];
lean_object* v_isHEq_3943_ = _args[1];
lean_object* v_lhs_3944_ = _args[2];
lean_object* v_rhs_3945_ = _args[3];
lean_object* v_lhsNode_3946_ = _args[4];
lean_object* v_rhsNode_3947_ = _args[5];
lean_object* v_lhsRoot_3948_ = _args[6];
lean_object* v_rhsRoot_3949_ = _args[7];
lean_object* v_flipped_3950_ = _args[8];
lean_object* v_a_3951_ = _args[9];
lean_object* v_a_3952_ = _args[10];
lean_object* v_a_3953_ = _args[11];
lean_object* v_a_3954_ = _args[12];
lean_object* v_a_3955_ = _args[13];
lean_object* v_a_3956_ = _args[14];
lean_object* v_a_3957_ = _args[15];
lean_object* v_a_3958_ = _args[16];
lean_object* v_a_3959_ = _args[17];
lean_object* v_a_3960_ = _args[18];
lean_object* v_a_3961_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3962_; uint8_t v_flipped_boxed_3963_; lean_object* v_res_3964_; 
v_isHEq_boxed_3962_ = lean_unbox(v_isHEq_3943_);
v_flipped_boxed_3963_ = lean_unbox(v_flipped_3950_);
v_res_3964_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3942_, v_isHEq_boxed_3962_, v_lhs_3944_, v_rhs_3945_, v_lhsNode_3946_, v_rhsNode_3947_, v_lhsRoot_3948_, v_rhsRoot_3949_, v_flipped_boxed_3963_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3951_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3965_, lean_object* v_as_x27_3966_, lean_object* v_b_3967_, lean_object* v_a_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3966_, v_b_3967_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3981_, lean_object* v_as_x27_3982_, lean_object* v_b_3983_, lean_object* v_a_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3981_, v_as_x27_3982_, v_b_3983_, v_a_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v_as_x27_3982_);
lean_dec(v_as_3981_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3997_, lean_object* v_as_x27_3998_, lean_object* v_b_3999_, lean_object* v_a_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3998_, v_b_3999_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4013_, lean_object* v_as_x27_4014_, lean_object* v_b_4015_, lean_object* v_a_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4013_, v_as_x27_4014_, v_b_4015_, v_a_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec(v_as_x27_4014_);
lean_dec(v_as_4013_);
return v_res_4028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4031_ = l_Lean_stringToMessageData(v___x_4030_);
return v___x_4031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4038_ = l_Lean_Name_append(v___x_4037_, v___x_4036_);
return v___x_4038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4041_ = l_Lean_stringToMessageData(v___x_4040_);
return v___x_4041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4044_ = l_Lean_stringToMessageData(v___x_4043_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4045_, lean_object* v_rhs_4046_, lean_object* v_proof_4047_, uint8_t v_isHEq_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_st_ref_get(v_a_4049_);
lean_inc_ref(v_lhs_4045_);
v___x_4064_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4063_, v_lhs_4045_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec(v___x_4063_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = lean_st_ref_get(v_a_4049_);
lean_inc_ref(v_rhs_4046_);
v___x_4067_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4066_, v_rhs_4046_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec(v___x_4066_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v_root_4069_; lean_object* v_root_4070_; size_t v___x_4071_; size_t v___x_4072_; uint8_t v___x_4073_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v_root_4069_ = lean_ctor_get(v_a_4065_, 2);
v_root_4070_ = lean_ctor_get(v_a_4068_, 2);
v___x_4071_ = lean_ptr_addr(v_root_4069_);
v___x_4072_ = lean_ptr_addr(v_root_4070_);
v___x_4073_ = lean_usize_dec_eq(v___x_4071_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_object* v_toCold_4074_; lean_object* v_options_4075_; lean_object* v_inheritedTraceOptions_4076_; uint8_t v_hasTrace_4077_; uint8_t v___x_4078_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4174_; uint8_t v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; uint8_t v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4206_; uint8_t v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; uint8_t v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4222_; lean_object* v_size_4223_; uint8_t v_interpreted_4224_; uint8_t v_ctor_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; uint8_t v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4242_; uint8_t v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; uint8_t v___y_4246_; lean_object* v___y_4247_; uint8_t v_ctor_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4264_; lean_object* v___y_4265_; uint8_t v_valueInconsistency_4266_; uint8_t v_trueEqFalse_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; 
v_toCold_4074_ = lean_ctor_get(v_a_4057_, 0);
v_options_4075_ = lean_ctor_get(v_toCold_4074_, 2);
v_inheritedTraceOptions_4076_ = lean_ctor_get(v_toCold_4074_, 11);
v_hasTrace_4077_ = lean_ctor_get_uint8(v_options_4075_, sizeof(void*)*1);
v___x_4078_ = 1;
if (v_hasTrace_4077_ == 0)
{
v___y_4323_ = v_a_4049_;
v___y_4324_ = v_a_4050_;
v___y_4325_ = v_a_4051_;
v___y_4326_ = v_a_4052_;
v___y_4327_ = v_a_4053_;
v___y_4328_ = v_a_4054_;
v___y_4329_ = v_a_4055_;
v___y_4330_ = v_a_4056_;
v___y_4331_ = v_a_4057_;
v___y_4332_ = v_a_4058_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4366_; lean_object* v_____do__lift_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4076_, v_options_4075_, v___x_4381_);
if (v___x_4382_ == 0)
{
v___y_4323_ = v_a_4049_;
v___y_4324_ = v_a_4050_;
v___y_4325_ = v_a_4051_;
v___y_4326_ = v_a_4052_;
v___y_4327_ = v_a_4053_;
v___y_4328_ = v_a_4054_;
v___y_4329_ = v_a_4055_;
v___y_4330_ = v_a_4056_;
v___y_4331_ = v_a_4057_;
v___y_4332_ = v_a_4058_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Meta_Grind_updateLastTag(v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_dec_ref_known(v___x_4383_, 1);
if (v_isHEq_4048_ == 0)
{
lean_object* v___x_4384_; 
lean_inc_ref(v_rhs_4046_);
lean_inc_ref(v_lhs_4045_);
v___x_4384_ = l_Lean_Meta_mkEq(v_lhs_4045_, v_rhs_4046_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v_____do__lift_4368_ = v_a_4385_;
v___y_4369_ = v_a_4049_;
v___y_4370_ = v_a_4050_;
v___y_4371_ = v_a_4051_;
v___y_4372_ = v_a_4052_;
v___y_4373_ = v_a_4053_;
v___y_4374_ = v_a_4054_;
v___y_4375_ = v_a_4055_;
v___y_4376_ = v_a_4056_;
v___y_4377_ = v_a_4057_;
v___y_4378_ = v_a_4058_;
goto v___jp_4367_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4386_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4384_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4384_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_object* v___x_4394_; 
lean_inc_ref(v_rhs_4046_);
lean_inc_ref(v_lhs_4045_);
v___x_4394_ = l_Lean_Meta_mkHEq(v_lhs_4045_, v_rhs_4046_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_____do__lift_4368_ = v_a_4395_;
v___y_4369_ = v_a_4049_;
v___y_4370_ = v_a_4050_;
v___y_4371_ = v_a_4051_;
v___y_4372_ = v_a_4052_;
v___y_4373_ = v_a_4053_;
v___y_4374_ = v_a_4054_;
v___y_4375_ = v_a_4055_;
v___y_4376_ = v_a_4056_;
v___y_4377_ = v_a_4057_;
v___y_4378_ = v_a_4058_;
goto v___jp_4367_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4396_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4394_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4394_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
else
{
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
return v___x_4383_;
}
}
v___jp_4367_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = l_Lean_MessageData_ofExpr(v_____do__lift_4368_);
v___x_4380_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4366_, v___x_4379_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
if (lean_obj_tag(v___x_4380_) == 0)
{
lean_dec_ref_known(v___x_4380_, 1);
v___y_4323_ = v___y_4369_;
v___y_4324_ = v___y_4370_;
v___y_4325_ = v___y_4371_;
v___y_4326_ = v___y_4372_;
v___y_4327_ = v___y_4373_;
v___y_4328_ = v___y_4374_;
v___y_4329_ = v___y_4375_;
v___y_4330_ = v___y_4376_;
v___y_4331_ = v___y_4377_;
v___y_4332_ = v___y_4378_;
goto v___jp_4322_;
}
else
{
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
return v___x_4380_;
}
}
}
v___jp_4079_:
{
lean_object* v_toCold_4090_; lean_object* v_options_4091_; uint8_t v_hasTrace_4092_; 
v_toCold_4090_ = lean_ctor_get(v___y_4088_, 0);
v_options_4091_ = lean_ctor_get(v_toCold_4090_, 2);
v_hasTrace_4092_ = lean_ctor_get_uint8(v_options_4091_, sizeof(void*)*1);
if (v_hasTrace_4092_ == 0)
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_Meta_Grind_checkInvariants(v___x_4073_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4093_;
}
else
{
lean_object* v_inheritedTraceOptions_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v_inheritedTraceOptions_4094_ = lean_ctor_get(v_toCold_4090_, 11);
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4094_, v_options_4091_, v___x_4096_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Meta_Grind_checkInvariants(v___x_4073_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Meta_Grind_updateLastTag(v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
lean_dec_ref_known(v___x_4099_, 1);
v___x_4100_ = lean_st_ref_get(v___y_4080_);
v___x_4101_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4100_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___x_4100_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v_a_4102_);
v___x_4105_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4095_, v___x_4104_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4105_, 1);
v___x_4106_ = l_Lean_Meta_Grind_checkInvariants(v___x_4073_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4106_;
}
else
{
return v___x_4105_;
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
v_a_4107_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4101_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4101_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
return v___x_4099_;
}
}
}
}
v___jp_4115_:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4119_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; uint8_t v___x_4131_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = lean_unbox(v_a_4130_);
lean_dec(v_a_4130_);
if (v___x_4131_ == 0)
{
if (v___y_4117_ == 0)
{
lean_dec_ref(v___y_4118_);
lean_dec_ref(v___y_4116_);
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
goto v___jp_4079_;
}
else
{
lean_object* v_self_4132_; lean_object* v_self_4133_; lean_object* v___x_4134_; 
v_self_4132_ = lean_ctor_get(v___y_4118_, 0);
lean_inc_ref(v_self_4132_);
lean_dec_ref(v___y_4118_);
v_self_4133_ = lean_ctor_get(v___y_4116_, 0);
lean_inc_ref(v_self_4133_);
lean_dec_ref(v___y_4116_);
v___x_4134_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4132_, v_self_4133_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
goto v___jp_4079_;
}
else
{
return v___x_4134_;
}
}
}
else
{
lean_dec_ref(v___y_4118_);
lean_dec_ref(v___y_4116_);
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
goto v___jp_4079_;
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___y_4118_);
lean_dec_ref(v___y_4116_);
v_a_4135_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4129_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4129_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
v___jp_4143_:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4147_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; uint8_t v___x_4159_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = lean_unbox(v_a_4158_);
lean_dec(v_a_4158_);
if (v___x_4159_ == 0)
{
uint8_t v_ctor_4160_; 
v_ctor_4160_ = lean_ctor_get_uint8(v___y_4146_, sizeof(void*)*12 + 2);
if (v_ctor_4160_ == 0)
{
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
else
{
uint8_t v_ctor_4161_; 
v_ctor_4161_ = lean_ctor_get_uint8(v___y_4144_, sizeof(void*)*12 + 2);
if (v_ctor_4161_ == 0)
{
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
else
{
lean_object* v_self_4162_; lean_object* v_self_4163_; lean_object* v___x_4164_; 
v_self_4162_ = lean_ctor_get(v___y_4146_, 0);
v_self_4163_ = lean_ctor_get(v___y_4144_, 0);
lean_inc_ref(v_self_4163_);
lean_inc_ref(v_self_4162_);
v___x_4164_ = l_Lean_Meta_Grind_propagateCtor(v_self_4162_, v_self_4163_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_dec_ref_known(v___x_4164_, 1);
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
else
{
lean_dec_ref(v___y_4146_);
lean_dec_ref(v___y_4144_);
return v___x_4164_;
}
}
}
}
else
{
v___y_4116_ = v___y_4144_;
v___y_4117_ = v___y_4145_;
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec_ref(v___y_4146_);
lean_dec_ref(v___y_4144_);
v_a_4165_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4157_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4157_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
v___jp_4173_:
{
if (v___y_4175_ == 0)
{
v___y_4144_ = v___y_4174_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
v___y_4151_ = v___y_4182_;
v___y_4152_ = v___y_4183_;
v___y_4153_ = v___y_4184_;
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___y_4186_;
v___y_4156_ = v___y_4187_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4188_; 
v___x_4188_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_dec_ref_known(v___x_4188_, 1);
v___y_4144_ = v___y_4174_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
v___y_4151_ = v___y_4182_;
v___y_4152_ = v___y_4183_;
v___y_4153_ = v___y_4184_;
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___y_4186_;
v___y_4156_ = v___y_4187_;
goto v___jp_4143_;
}
else
{
lean_dec_ref(v___y_4177_);
lean_dec_ref(v___y_4174_);
return v___x_4188_;
}
}
}
v___jp_4189_:
{
lean_object* v___x_4204_; 
lean_inc_ref(v___y_4195_);
lean_inc_ref(v___y_4190_);
v___x_4204_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4047_, v_isHEq_4048_, v_rhs_4046_, v_lhs_4045_, v_a_4068_, v_a_4065_, v___y_4190_, v___y_4195_, v___x_4078_, v___y_4199_, v___y_4203_, v___y_4202_, v___y_4198_, v___y_4200_, v___y_4192_, v___y_4201_, v___y_4196_, v___y_4197_, v___y_4193_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_dec_ref_known(v___x_4204_, 1);
v___y_4174_ = v___y_4190_;
v___y_4175_ = v___y_4191_;
v___y_4176_ = v___y_4194_;
v___y_4177_ = v___y_4195_;
v___y_4178_ = v___y_4199_;
v___y_4179_ = v___y_4203_;
v___y_4180_ = v___y_4202_;
v___y_4181_ = v___y_4198_;
v___y_4182_ = v___y_4200_;
v___y_4183_ = v___y_4192_;
v___y_4184_ = v___y_4201_;
v___y_4185_ = v___y_4196_;
v___y_4186_ = v___y_4197_;
v___y_4187_ = v___y_4193_;
goto v___jp_4173_;
}
else
{
lean_dec_ref(v___y_4195_);
lean_dec_ref(v___y_4190_);
return v___x_4204_;
}
}
v___jp_4205_:
{
lean_object* v___x_4220_; 
lean_inc_ref(v___y_4206_);
lean_inc_ref(v___y_4211_);
v___x_4220_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4047_, v_isHEq_4048_, v_lhs_4045_, v_rhs_4046_, v_a_4065_, v_a_4068_, v___y_4211_, v___y_4206_, v___x_4073_, v___y_4215_, v___y_4219_, v___y_4218_, v___y_4214_, v___y_4216_, v___y_4208_, v___y_4217_, v___y_4212_, v___y_4213_, v___y_4209_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_dec_ref_known(v___x_4220_, 1);
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4210_;
v___y_4177_ = v___y_4211_;
v___y_4178_ = v___y_4215_;
v___y_4179_ = v___y_4219_;
v___y_4180_ = v___y_4218_;
v___y_4181_ = v___y_4214_;
v___y_4182_ = v___y_4216_;
v___y_4183_ = v___y_4208_;
v___y_4184_ = v___y_4217_;
v___y_4185_ = v___y_4212_;
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4209_;
goto v___jp_4173_;
}
else
{
lean_dec_ref(v___y_4211_);
lean_dec_ref(v___y_4206_);
return v___x_4220_;
}
}
v___jp_4221_:
{
lean_object* v_size_4239_; uint8_t v___x_4240_; 
v_size_4239_ = lean_ctor_get(v___y_4230_, 6);
v___x_4240_ = lean_nat_dec_lt(v_size_4223_, v_size_4239_);
lean_dec(v_size_4223_);
if (v___x_4240_ == 0)
{
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
v___y_4211_ = v___y_4230_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
v___y_4214_ = v___y_4233_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4237_;
v___y_4219_ = v___y_4238_;
goto v___jp_4205_;
}
else
{
if (v_interpreted_4224_ == 0)
{
if (v_ctor_4225_ == 0)
{
v___y_4190_ = v___y_4222_;
v___y_4191_ = v___y_4226_;
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4228_;
v___y_4194_ = v___y_4229_;
v___y_4195_ = v___y_4230_;
v___y_4196_ = v___y_4231_;
v___y_4197_ = v___y_4232_;
v___y_4198_ = v___y_4233_;
v___y_4199_ = v___y_4234_;
v___y_4200_ = v___y_4235_;
v___y_4201_ = v___y_4236_;
v___y_4202_ = v___y_4237_;
v___y_4203_ = v___y_4238_;
goto v___jp_4189_;
}
else
{
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
v___y_4211_ = v___y_4230_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
v___y_4214_ = v___y_4233_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4237_;
v___y_4219_ = v___y_4238_;
goto v___jp_4205_;
}
}
else
{
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
v___y_4211_ = v___y_4230_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
v___y_4214_ = v___y_4233_;
v___y_4215_ = v___y_4234_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4237_;
v___y_4219_ = v___y_4238_;
goto v___jp_4205_;
}
}
}
v___jp_4241_:
{
if (v_ctor_4248_ == 0)
{
lean_object* v_size_4257_; uint8_t v_interpreted_4258_; uint8_t v_ctor_4259_; 
v_size_4257_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4257_);
v_interpreted_4258_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v_ctor_4259_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
v___y_4222_ = v___y_4242_;
v_size_4223_ = v_size_4257_;
v_interpreted_4224_ = v_interpreted_4258_;
v_ctor_4225_ = v_ctor_4259_;
v___y_4226_ = v___y_4243_;
v___y_4227_ = v___y_4244_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v___y_4246_;
v___y_4230_ = v___y_4247_;
v___y_4231_ = v___y_4249_;
v___y_4232_ = v___y_4250_;
v___y_4233_ = v___y_4251_;
v___y_4234_ = v___y_4252_;
v___y_4235_ = v___y_4253_;
v___y_4236_ = v___y_4254_;
v___y_4237_ = v___y_4255_;
v___y_4238_ = v___y_4256_;
goto v___jp_4221_;
}
else
{
uint8_t v_ctor_4260_; 
v_ctor_4260_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
if (v_ctor_4260_ == 0)
{
v___y_4190_ = v___y_4242_;
v___y_4191_ = v___y_4243_;
v___y_4192_ = v___y_4244_;
v___y_4193_ = v___y_4245_;
v___y_4194_ = v___y_4246_;
v___y_4195_ = v___y_4247_;
v___y_4196_ = v___y_4249_;
v___y_4197_ = v___y_4250_;
v___y_4198_ = v___y_4251_;
v___y_4199_ = v___y_4252_;
v___y_4200_ = v___y_4253_;
v___y_4201_ = v___y_4254_;
v___y_4202_ = v___y_4255_;
v___y_4203_ = v___y_4256_;
goto v___jp_4189_;
}
else
{
lean_object* v_size_4261_; uint8_t v_interpreted_4262_; 
v_size_4261_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4261_);
v_interpreted_4262_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v___y_4222_ = v___y_4242_;
v_size_4223_ = v_size_4261_;
v_interpreted_4224_ = v_interpreted_4262_;
v_ctor_4225_ = v_ctor_4260_;
v___y_4226_ = v___y_4243_;
v___y_4227_ = v___y_4244_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v___y_4246_;
v___y_4230_ = v___y_4247_;
v___y_4231_ = v___y_4249_;
v___y_4232_ = v___y_4250_;
v___y_4233_ = v___y_4251_;
v___y_4234_ = v___y_4252_;
v___y_4235_ = v___y_4253_;
v___y_4236_ = v___y_4254_;
v___y_4237_ = v___y_4255_;
v___y_4238_ = v___y_4256_;
goto v___jp_4221_;
}
}
}
v___jp_4263_:
{
uint8_t v_interpreted_4278_; 
v_interpreted_4278_ = lean_ctor_get_uint8(v___y_4265_, sizeof(void*)*12 + 1);
if (v_interpreted_4278_ == 0)
{
uint8_t v_ctor_4279_; 
v_ctor_4279_ = lean_ctor_get_uint8(v___y_4265_, sizeof(void*)*12 + 2);
v___y_4242_ = v___y_4264_;
v___y_4243_ = v_trueEqFalse_4267_;
v___y_4244_ = v___y_4273_;
v___y_4245_ = v___y_4277_;
v___y_4246_ = v_valueInconsistency_4266_;
v___y_4247_ = v___y_4265_;
v_ctor_4248_ = v_ctor_4279_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4276_;
v___y_4251_ = v___y_4271_;
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___y_4272_;
v___y_4254_ = v___y_4274_;
v___y_4255_ = v___y_4270_;
v___y_4256_ = v___y_4269_;
goto v___jp_4241_;
}
else
{
uint8_t v_interpreted_4280_; 
v_interpreted_4280_ = lean_ctor_get_uint8(v___y_4264_, sizeof(void*)*12 + 1);
if (v_interpreted_4280_ == 0)
{
v___y_4190_ = v___y_4264_;
v___y_4191_ = v_trueEqFalse_4267_;
v___y_4192_ = v___y_4273_;
v___y_4193_ = v___y_4277_;
v___y_4194_ = v_valueInconsistency_4266_;
v___y_4195_ = v___y_4265_;
v___y_4196_ = v___y_4275_;
v___y_4197_ = v___y_4276_;
v___y_4198_ = v___y_4271_;
v___y_4199_ = v___y_4268_;
v___y_4200_ = v___y_4272_;
v___y_4201_ = v___y_4274_;
v___y_4202_ = v___y_4270_;
v___y_4203_ = v___y_4269_;
goto v___jp_4189_;
}
else
{
uint8_t v_ctor_4281_; 
v_ctor_4281_ = lean_ctor_get_uint8(v___y_4265_, sizeof(void*)*12 + 2);
v___y_4242_ = v___y_4264_;
v___y_4243_ = v_trueEqFalse_4267_;
v___y_4244_ = v___y_4273_;
v___y_4245_ = v___y_4277_;
v___y_4246_ = v_valueInconsistency_4266_;
v___y_4247_ = v___y_4265_;
v_ctor_4248_ = v_ctor_4281_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4276_;
v___y_4251_ = v___y_4271_;
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___y_4272_;
v___y_4254_ = v___y_4274_;
v___y_4255_ = v___y_4270_;
v___y_4256_ = v___y_4269_;
goto v___jp_4241_;
}
}
}
v___jp_4282_:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4293_, v___y_4287_, v___y_4291_, v___y_4294_, v___y_4288_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_dec_ref_known(v___x_4295_, 1);
v___y_4264_ = v___y_4283_;
v___y_4265_ = v___y_4290_;
v_valueInconsistency_4266_ = v___x_4073_;
v_trueEqFalse_4267_ = v___x_4078_;
v___y_4268_ = v___y_4293_;
v___y_4269_ = v___y_4284_;
v___y_4270_ = v___y_4292_;
v___y_4271_ = v___y_4285_;
v___y_4272_ = v___y_4289_;
v___y_4273_ = v___y_4286_;
v___y_4274_ = v___y_4287_;
v___y_4275_ = v___y_4291_;
v___y_4276_ = v___y_4294_;
v___y_4277_ = v___y_4288_;
goto v___jp_4263_;
}
else
{
lean_dec_ref(v___y_4290_);
lean_dec_ref(v___y_4283_);
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
return v___x_4295_;
}
}
v___jp_4296_:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Lean_Meta_Grind_hasSameType(v___y_4298_, v___y_4302_, v___y_4303_, v___y_4307_, v___y_4310_, v___y_4304_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; uint8_t v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = lean_unbox(v_a_4312_);
lean_dec(v_a_4312_);
if (v___x_4313_ == 0)
{
v___y_4264_ = v___y_4297_;
v___y_4265_ = v___y_4306_;
v_valueInconsistency_4266_ = v___x_4073_;
v_trueEqFalse_4267_ = v___x_4073_;
v___y_4268_ = v___y_4309_;
v___y_4269_ = v___y_4299_;
v___y_4270_ = v___y_4308_;
v___y_4271_ = v___y_4300_;
v___y_4272_ = v___y_4305_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___y_4307_;
v___y_4276_ = v___y_4310_;
v___y_4277_ = v___y_4304_;
goto v___jp_4263_;
}
else
{
v___y_4264_ = v___y_4297_;
v___y_4265_ = v___y_4306_;
v_valueInconsistency_4266_ = v___x_4078_;
v_trueEqFalse_4267_ = v___x_4073_;
v___y_4268_ = v___y_4309_;
v___y_4269_ = v___y_4299_;
v___y_4270_ = v___y_4308_;
v___y_4271_ = v___y_4300_;
v___y_4272_ = v___y_4305_;
v___y_4273_ = v___y_4301_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___y_4307_;
v___y_4276_ = v___y_4310_;
v___y_4277_ = v___y_4304_;
goto v___jp_4263_;
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4297_);
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4314_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4311_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4311_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
v___jp_4322_:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = lean_st_ref_get(v___y_4323_);
lean_inc_ref(v_root_4069_);
v___x_4334_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4333_, v_root_4069_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
lean_dec(v___x_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
v___x_4336_ = lean_st_ref_get(v___y_4323_);
lean_inc_ref(v_root_4070_);
v___x_4337_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4336_, v_root_4070_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
lean_dec(v___x_4336_);
if (lean_obj_tag(v___x_4337_) == 0)
{
uint8_t v_interpreted_4338_; 
v_interpreted_4338_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 1);
if (v_interpreted_4338_ == 0)
{
lean_object* v_a_4339_; uint8_t v_ctor_4340_; 
v_a_4339_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4339_);
lean_dec_ref_known(v___x_4337_, 1);
v_ctor_4340_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 2);
v___y_4242_ = v_a_4339_;
v___y_4243_ = v___x_4073_;
v___y_4244_ = v___y_4328_;
v___y_4245_ = v___y_4332_;
v___y_4246_ = v___x_4073_;
v___y_4247_ = v_a_4335_;
v_ctor_4248_ = v_ctor_4340_;
v___y_4249_ = v___y_4330_;
v___y_4250_ = v___y_4331_;
v___y_4251_ = v___y_4326_;
v___y_4252_ = v___y_4323_;
v___y_4253_ = v___y_4327_;
v___y_4254_ = v___y_4329_;
v___y_4255_ = v___y_4325_;
v___y_4256_ = v___y_4324_;
goto v___jp_4241_;
}
else
{
lean_object* v_a_4341_; uint8_t v_interpreted_4342_; 
v_a_4341_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4337_, 1);
v_interpreted_4342_ = lean_ctor_get_uint8(v_a_4341_, sizeof(void*)*12 + 1);
if (v_interpreted_4342_ == 0)
{
v___y_4190_ = v_a_4341_;
v___y_4191_ = v___x_4073_;
v___y_4192_ = v___y_4328_;
v___y_4193_ = v___y_4332_;
v___y_4194_ = v___x_4073_;
v___y_4195_ = v_a_4335_;
v___y_4196_ = v___y_4330_;
v___y_4197_ = v___y_4331_;
v___y_4198_ = v___y_4326_;
v___y_4199_ = v___y_4323_;
v___y_4200_ = v___y_4327_;
v___y_4201_ = v___y_4329_;
v___y_4202_ = v___y_4325_;
v___y_4203_ = v___y_4324_;
goto v___jp_4189_;
}
else
{
lean_object* v_self_4343_; uint8_t v_ctor_4344_; uint8_t v_heqProofs_4345_; lean_object* v_self_4346_; uint8_t v_heqProofs_4347_; uint8_t v___x_4348_; 
v_self_4343_ = lean_ctor_get(v_a_4335_, 0);
v_ctor_4344_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 2);
v_heqProofs_4345_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 4);
v_self_4346_ = lean_ctor_get(v_a_4341_, 0);
v_heqProofs_4347_ = lean_ctor_get_uint8(v_a_4341_, sizeof(void*)*12 + 4);
v___x_4348_ = l_Lean_Expr_isTrue(v_root_4069_);
if (v___x_4348_ == 0)
{
uint8_t v___x_4349_; 
v___x_4349_ = l_Lean_Expr_isTrue(v_root_4070_);
if (v___x_4349_ == 0)
{
if (v_isHEq_4048_ == 0)
{
if (v_heqProofs_4345_ == 0)
{
if (v_heqProofs_4347_ == 0)
{
v___y_4242_ = v_a_4341_;
v___y_4243_ = v___x_4073_;
v___y_4244_ = v___y_4328_;
v___y_4245_ = v___y_4332_;
v___y_4246_ = v___x_4078_;
v___y_4247_ = v_a_4335_;
v_ctor_4248_ = v_ctor_4344_;
v___y_4249_ = v___y_4330_;
v___y_4250_ = v___y_4331_;
v___y_4251_ = v___y_4326_;
v___y_4252_ = v___y_4323_;
v___y_4253_ = v___y_4327_;
v___y_4254_ = v___y_4329_;
v___y_4255_ = v___y_4325_;
v___y_4256_ = v___y_4324_;
goto v___jp_4241_;
}
else
{
lean_inc_ref(v_self_4346_);
lean_inc_ref(v_self_4343_);
v___y_4297_ = v_a_4341_;
v___y_4298_ = v_self_4343_;
v___y_4299_ = v___y_4324_;
v___y_4300_ = v___y_4326_;
v___y_4301_ = v___y_4328_;
v___y_4302_ = v_self_4346_;
v___y_4303_ = v___y_4329_;
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4327_;
v___y_4306_ = v_a_4335_;
v___y_4307_ = v___y_4330_;
v___y_4308_ = v___y_4325_;
v___y_4309_ = v___y_4323_;
v___y_4310_ = v___y_4331_;
goto v___jp_4296_;
}
}
else
{
lean_inc_ref(v_self_4346_);
lean_inc_ref(v_self_4343_);
v___y_4297_ = v_a_4341_;
v___y_4298_ = v_self_4343_;
v___y_4299_ = v___y_4324_;
v___y_4300_ = v___y_4326_;
v___y_4301_ = v___y_4328_;
v___y_4302_ = v_self_4346_;
v___y_4303_ = v___y_4329_;
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4327_;
v___y_4306_ = v_a_4335_;
v___y_4307_ = v___y_4330_;
v___y_4308_ = v___y_4325_;
v___y_4309_ = v___y_4323_;
v___y_4310_ = v___y_4331_;
goto v___jp_4296_;
}
}
else
{
lean_inc_ref(v_self_4346_);
lean_inc_ref(v_self_4343_);
v___y_4297_ = v_a_4341_;
v___y_4298_ = v_self_4343_;
v___y_4299_ = v___y_4324_;
v___y_4300_ = v___y_4326_;
v___y_4301_ = v___y_4328_;
v___y_4302_ = v_self_4346_;
v___y_4303_ = v___y_4329_;
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4327_;
v___y_4306_ = v_a_4335_;
v___y_4307_ = v___y_4330_;
v___y_4308_ = v___y_4325_;
v___y_4309_ = v___y_4323_;
v___y_4310_ = v___y_4331_;
goto v___jp_4296_;
}
}
else
{
v___y_4283_ = v_a_4341_;
v___y_4284_ = v___y_4324_;
v___y_4285_ = v___y_4326_;
v___y_4286_ = v___y_4328_;
v___y_4287_ = v___y_4329_;
v___y_4288_ = v___y_4332_;
v___y_4289_ = v___y_4327_;
v___y_4290_ = v_a_4335_;
v___y_4291_ = v___y_4330_;
v___y_4292_ = v___y_4325_;
v___y_4293_ = v___y_4323_;
v___y_4294_ = v___y_4331_;
goto v___jp_4282_;
}
}
else
{
v___y_4283_ = v_a_4341_;
v___y_4284_ = v___y_4324_;
v___y_4285_ = v___y_4326_;
v___y_4286_ = v___y_4328_;
v___y_4287_ = v___y_4329_;
v___y_4288_ = v___y_4332_;
v___y_4289_ = v___y_4327_;
v___y_4290_ = v_a_4335_;
v___y_4291_ = v___y_4330_;
v___y_4292_ = v___y_4325_;
v___y_4293_ = v___y_4323_;
v___y_4294_ = v___y_4331_;
goto v___jp_4282_;
}
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v_a_4335_);
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4350_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4337_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4337_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4358_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4334_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4334_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
else
{
lean_object* v_toCold_4404_; lean_object* v_options_4405_; uint8_t v_hasTrace_4406_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
v_toCold_4404_ = lean_ctor_get(v_a_4057_, 0);
v_options_4405_ = lean_ctor_get(v_toCold_4404_, 2);
v_hasTrace_4406_ = lean_ctor_get_uint8(v_options_4405_, sizeof(void*)*1);
if (v_hasTrace_4406_ == 0)
{
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
goto v___jp_4060_;
}
else
{
lean_object* v_inheritedTraceOptions_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; uint8_t v___x_4410_; 
v_inheritedTraceOptions_4407_ = lean_ctor_get(v_toCold_4404_, 11);
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4407_, v_options_4405_, v___x_4409_);
if (v___x_4410_ == 0)
{
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
goto v___jp_4060_;
}
else
{
lean_object* v___x_4411_; 
v___x_4411_ = l_Lean_Meta_Grind_updateLastTag(v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v___x_4412_; 
lean_dec_ref_known(v___x_4411_, 1);
v___x_4412_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4045_, v_a_4049_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4046_, v_a_4049_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref_known(v___x_4414_, 1);
v___x_4416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4417_, 0, v_a_4413_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
lean_ctor_set(v___x_4418_, 1, v_a_4415_);
v___x_4419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4408_, v___x_4420_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_dec_ref_known(v___x_4421_, 1);
goto v___jp_4060_;
}
else
{
return v___x_4421_;
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_a_4413_);
v_a_4422_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4414_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4414_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec_ref(v_rhs_4046_);
v_a_4430_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4412_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4412_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
return v___x_4411_;
}
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_a_4065_);
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4438_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4067_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4067_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec_ref(v_proof_4047_);
lean_dec_ref(v_rhs_4046_);
lean_dec_ref(v_lhs_4045_);
v_a_4446_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4064_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4064_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
v___jp_4060_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_box(0);
v___x_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
return v___x_4062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4454_, lean_object* v_rhs_4455_, lean_object* v_proof_4456_, lean_object* v_isHEq_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
uint8_t v_isHEq_boxed_4469_; lean_object* v_res_4470_; 
v_isHEq_boxed_4469_ = lean_unbox(v_isHEq_4457_);
v_res_4470_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4454_, v_rhs_4455_, v_proof_4456_, v_isHEq_boxed_4469_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec(v_a_4458_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v_toGoalState_4476_; lean_object* v_mvarId_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4517_; 
v___x_4475_ = lean_st_ref_take(v_a_4473_);
v_toGoalState_4476_ = lean_ctor_get(v___x_4475_, 0);
v_mvarId_4477_ = lean_ctor_get(v___x_4475_, 1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4479_ = v___x_4475_;
v_isShared_4480_ = v_isSharedCheck_4517_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_mvarId_4477_);
lean_inc(v_toGoalState_4476_);
lean_dec(v___x_4475_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4517_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v_nextDeclIdx_4481_; lean_object* v_enodeMap_4482_; lean_object* v_exprs_4483_; lean_object* v_parents_4484_; lean_object* v_congrTable_4485_; lean_object* v_appMap_4486_; lean_object* v_indicesFound_4487_; lean_object* v_internalizing_4488_; uint8_t v_inconsistent_4489_; lean_object* v_nextIdx_4490_; lean_object* v_newRawFacts_4491_; lean_object* v_facts_4492_; lean_object* v_extThms_4493_; lean_object* v_ematch_4494_; lean_object* v_inj_4495_; lean_object* v_split_4496_; lean_object* v_clean_4497_; lean_object* v_sstates_4498_; lean_object* v_goalStack_4499_; uint64_t v_introBase_4500_; lean_object* v_numIntros_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4515_; 
v_nextDeclIdx_4481_ = lean_ctor_get(v_toGoalState_4476_, 0);
v_enodeMap_4482_ = lean_ctor_get(v_toGoalState_4476_, 1);
v_exprs_4483_ = lean_ctor_get(v_toGoalState_4476_, 2);
v_parents_4484_ = lean_ctor_get(v_toGoalState_4476_, 3);
v_congrTable_4485_ = lean_ctor_get(v_toGoalState_4476_, 4);
v_appMap_4486_ = lean_ctor_get(v_toGoalState_4476_, 5);
v_indicesFound_4487_ = lean_ctor_get(v_toGoalState_4476_, 6);
v_internalizing_4488_ = lean_ctor_get(v_toGoalState_4476_, 8);
v_inconsistent_4489_ = lean_ctor_get_uint8(v_toGoalState_4476_, sizeof(void*)*20 + 8);
v_nextIdx_4490_ = lean_ctor_get(v_toGoalState_4476_, 9);
v_newRawFacts_4491_ = lean_ctor_get(v_toGoalState_4476_, 10);
v_facts_4492_ = lean_ctor_get(v_toGoalState_4476_, 11);
v_extThms_4493_ = lean_ctor_get(v_toGoalState_4476_, 12);
v_ematch_4494_ = lean_ctor_get(v_toGoalState_4476_, 13);
v_inj_4495_ = lean_ctor_get(v_toGoalState_4476_, 14);
v_split_4496_ = lean_ctor_get(v_toGoalState_4476_, 15);
v_clean_4497_ = lean_ctor_get(v_toGoalState_4476_, 16);
v_sstates_4498_ = lean_ctor_get(v_toGoalState_4476_, 17);
v_goalStack_4499_ = lean_ctor_get(v_toGoalState_4476_, 18);
v_introBase_4500_ = lean_ctor_get_uint64(v_toGoalState_4476_, sizeof(void*)*20);
v_numIntros_4501_ = lean_ctor_get(v_toGoalState_4476_, 19);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_toGoalState_4476_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_toGoalState_4476_, 7);
lean_dec(v_unused_4516_);
v___x_4503_ = v_toGoalState_4476_;
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_numIntros_4501_);
lean_inc(v_goalStack_4499_);
lean_inc(v_sstates_4498_);
lean_inc(v_clean_4497_);
lean_inc(v_split_4496_);
lean_inc(v_inj_4495_);
lean_inc(v_ematch_4494_);
lean_inc(v_extThms_4493_);
lean_inc(v_facts_4492_);
lean_inc(v_newRawFacts_4491_);
lean_inc(v_nextIdx_4490_);
lean_inc(v_internalizing_4488_);
lean_inc(v_indicesFound_4487_);
lean_inc(v_appMap_4486_);
lean_inc(v_congrTable_4485_);
lean_inc(v_parents_4484_);
lean_inc(v_exprs_4483_);
lean_inc(v_enodeMap_4482_);
lean_inc(v_nextDeclIdx_4481_);
lean_dec(v_toGoalState_4476_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4505_ = lean_box(0);
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 7, v___x_4506_);
v___x_4508_ = v___x_4503_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_nextDeclIdx_4481_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_enodeMap_4482_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_exprs_4483_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_parents_4484_);
lean_ctor_set(v_reuseFailAlloc_4514_, 4, v_congrTable_4485_);
lean_ctor_set(v_reuseFailAlloc_4514_, 5, v_appMap_4486_);
lean_ctor_set(v_reuseFailAlloc_4514_, 6, v_indicesFound_4487_);
lean_ctor_set(v_reuseFailAlloc_4514_, 7, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4514_, 8, v_internalizing_4488_);
lean_ctor_set(v_reuseFailAlloc_4514_, 9, v_nextIdx_4490_);
lean_ctor_set(v_reuseFailAlloc_4514_, 10, v_newRawFacts_4491_);
lean_ctor_set(v_reuseFailAlloc_4514_, 11, v_facts_4492_);
lean_ctor_set(v_reuseFailAlloc_4514_, 12, v_extThms_4493_);
lean_ctor_set(v_reuseFailAlloc_4514_, 13, v_ematch_4494_);
lean_ctor_set(v_reuseFailAlloc_4514_, 14, v_inj_4495_);
lean_ctor_set(v_reuseFailAlloc_4514_, 15, v_split_4496_);
lean_ctor_set(v_reuseFailAlloc_4514_, 16, v_clean_4497_);
lean_ctor_set(v_reuseFailAlloc_4514_, 17, v_sstates_4498_);
lean_ctor_set(v_reuseFailAlloc_4514_, 18, v_goalStack_4499_);
lean_ctor_set(v_reuseFailAlloc_4514_, 19, v_numIntros_4501_);
lean_ctor_set_uint8(v_reuseFailAlloc_4514_, sizeof(void*)*20 + 8, v_inconsistent_4489_);
lean_ctor_set_uint64(v_reuseFailAlloc_4514_, sizeof(void*)*20, v_introBase_4500_);
v___x_4508_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___x_4508_);
v___x_4510_ = v___x_4479_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_mvarId_4477_);
v___x_4510_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = lean_st_ref_put(v_a_4473_, v___x_4510_);
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4505_);
return v___x_4512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4518_);
lean_dec(v_a_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4521_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec(v_a_4533_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; lean_object* v_toGoalState_4548_; lean_object* v_toProcess_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; uint8_t v___x_4553_; 
v___x_4547_ = lean_st_ref_get(v_a_4545_);
v_toGoalState_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_ref(v_toGoalState_4548_);
lean_dec(v___x_4547_);
v_toProcess_4549_ = lean_ctor_get(v_toGoalState_4548_, 7);
lean_inc_ref(v_toProcess_4549_);
lean_dec_ref(v_toGoalState_4548_);
v___x_4550_ = lean_array_get_size(v_toProcess_4549_);
v___x_4551_ = lean_unsigned_to_nat(1u);
v___x_4552_ = lean_nat_sub(v___x_4550_, v___x_4551_);
v___x_4553_ = lean_nat_dec_lt(v___x_4552_, v___x_4550_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
lean_dec(v___x_4552_);
lean_dec_ref(v_toProcess_4549_);
v___x_4554_ = lean_box(0);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v_toGoalState_4559_; lean_object* v_mvarId_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4599_; 
v___x_4556_ = lean_array_fget(v_toProcess_4549_, v___x_4552_);
lean_dec(v___x_4552_);
lean_dec_ref(v_toProcess_4549_);
v___x_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___x_4558_ = lean_st_ref_take(v_a_4545_);
v_toGoalState_4559_ = lean_ctor_get(v___x_4558_, 0);
v_mvarId_4560_ = lean_ctor_get(v___x_4558_, 1);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4562_ = v___x_4558_;
v_isShared_4563_ = v_isSharedCheck_4599_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_mvarId_4560_);
lean_inc(v_toGoalState_4559_);
lean_dec(v___x_4558_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4599_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v_nextDeclIdx_4564_; lean_object* v_enodeMap_4565_; lean_object* v_exprs_4566_; lean_object* v_parents_4567_; lean_object* v_congrTable_4568_; lean_object* v_appMap_4569_; lean_object* v_indicesFound_4570_; lean_object* v_toProcess_4571_; lean_object* v_internalizing_4572_; uint8_t v_inconsistent_4573_; lean_object* v_nextIdx_4574_; lean_object* v_newRawFacts_4575_; lean_object* v_facts_4576_; lean_object* v_extThms_4577_; lean_object* v_ematch_4578_; lean_object* v_inj_4579_; lean_object* v_split_4580_; lean_object* v_clean_4581_; lean_object* v_sstates_4582_; lean_object* v_goalStack_4583_; uint64_t v_introBase_4584_; lean_object* v_numIntros_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4598_; 
v_nextDeclIdx_4564_ = lean_ctor_get(v_toGoalState_4559_, 0);
v_enodeMap_4565_ = lean_ctor_get(v_toGoalState_4559_, 1);
v_exprs_4566_ = lean_ctor_get(v_toGoalState_4559_, 2);
v_parents_4567_ = lean_ctor_get(v_toGoalState_4559_, 3);
v_congrTable_4568_ = lean_ctor_get(v_toGoalState_4559_, 4);
v_appMap_4569_ = lean_ctor_get(v_toGoalState_4559_, 5);
v_indicesFound_4570_ = lean_ctor_get(v_toGoalState_4559_, 6);
v_toProcess_4571_ = lean_ctor_get(v_toGoalState_4559_, 7);
v_internalizing_4572_ = lean_ctor_get(v_toGoalState_4559_, 8);
v_inconsistent_4573_ = lean_ctor_get_uint8(v_toGoalState_4559_, sizeof(void*)*20 + 8);
v_nextIdx_4574_ = lean_ctor_get(v_toGoalState_4559_, 9);
v_newRawFacts_4575_ = lean_ctor_get(v_toGoalState_4559_, 10);
v_facts_4576_ = lean_ctor_get(v_toGoalState_4559_, 11);
v_extThms_4577_ = lean_ctor_get(v_toGoalState_4559_, 12);
v_ematch_4578_ = lean_ctor_get(v_toGoalState_4559_, 13);
v_inj_4579_ = lean_ctor_get(v_toGoalState_4559_, 14);
v_split_4580_ = lean_ctor_get(v_toGoalState_4559_, 15);
v_clean_4581_ = lean_ctor_get(v_toGoalState_4559_, 16);
v_sstates_4582_ = lean_ctor_get(v_toGoalState_4559_, 17);
v_goalStack_4583_ = lean_ctor_get(v_toGoalState_4559_, 18);
v_introBase_4584_ = lean_ctor_get_uint64(v_toGoalState_4559_, sizeof(void*)*20);
v_numIntros_4585_ = lean_ctor_get(v_toGoalState_4559_, 19);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_toGoalState_4559_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4587_ = v_toGoalState_4559_;
v_isShared_4588_ = v_isSharedCheck_4598_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_numIntros_4585_);
lean_inc(v_goalStack_4583_);
lean_inc(v_sstates_4582_);
lean_inc(v_clean_4581_);
lean_inc(v_split_4580_);
lean_inc(v_inj_4579_);
lean_inc(v_ematch_4578_);
lean_inc(v_extThms_4577_);
lean_inc(v_facts_4576_);
lean_inc(v_newRawFacts_4575_);
lean_inc(v_nextIdx_4574_);
lean_inc(v_internalizing_4572_);
lean_inc(v_toProcess_4571_);
lean_inc(v_indicesFound_4570_);
lean_inc(v_appMap_4569_);
lean_inc(v_congrTable_4568_);
lean_inc(v_parents_4567_);
lean_inc(v_exprs_4566_);
lean_inc(v_enodeMap_4565_);
lean_inc(v_nextDeclIdx_4564_);
lean_dec(v_toGoalState_4559_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4598_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
v___x_4589_ = lean_array_pop(v_toProcess_4571_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 7, v___x_4589_);
v___x_4591_ = v___x_4587_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_nextDeclIdx_4564_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_enodeMap_4565_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_exprs_4566_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_parents_4567_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_congrTable_4568_);
lean_ctor_set(v_reuseFailAlloc_4597_, 5, v_appMap_4569_);
lean_ctor_set(v_reuseFailAlloc_4597_, 6, v_indicesFound_4570_);
lean_ctor_set(v_reuseFailAlloc_4597_, 7, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4597_, 8, v_internalizing_4572_);
lean_ctor_set(v_reuseFailAlloc_4597_, 9, v_nextIdx_4574_);
lean_ctor_set(v_reuseFailAlloc_4597_, 10, v_newRawFacts_4575_);
lean_ctor_set(v_reuseFailAlloc_4597_, 11, v_facts_4576_);
lean_ctor_set(v_reuseFailAlloc_4597_, 12, v_extThms_4577_);
lean_ctor_set(v_reuseFailAlloc_4597_, 13, v_ematch_4578_);
lean_ctor_set(v_reuseFailAlloc_4597_, 14, v_inj_4579_);
lean_ctor_set(v_reuseFailAlloc_4597_, 15, v_split_4580_);
lean_ctor_set(v_reuseFailAlloc_4597_, 16, v_clean_4581_);
lean_ctor_set(v_reuseFailAlloc_4597_, 17, v_sstates_4582_);
lean_ctor_set(v_reuseFailAlloc_4597_, 18, v_goalStack_4583_);
lean_ctor_set(v_reuseFailAlloc_4597_, 19, v_numIntros_4585_);
lean_ctor_set_uint8(v_reuseFailAlloc_4597_, sizeof(void*)*20 + 8, v_inconsistent_4573_);
lean_ctor_set_uint64(v_reuseFailAlloc_4597_, sizeof(void*)*20, v_introBase_4584_);
v___x_4591_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_object* v___x_4593_; 
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v___x_4591_);
v___x_4593_ = v___x_4562_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_mvarId_4560_);
v___x_4593_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = lean_st_ref_put(v_a_4545_, v___x_4593_);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4557_);
return v___x_4595_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4600_);
lean_dec(v_a_4600_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4603_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec(v_a_4615_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4627_, lean_object* v_rhs_4628_, lean_object* v_proof_4629_, uint8_t v_isHEq_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4627_, v_rhs_4628_, v_proof_4629_, v_isHEq_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v___x_4643_; 
lean_dec_ref_known(v___x_4642_, 1);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
lean_inc(v_a_4638_);
lean_inc_ref(v_a_4637_);
lean_inc(v_a_4636_);
lean_inc_ref(v_a_4635_);
lean_inc(v_a_4634_);
lean_inc_ref(v_a_4633_);
lean_inc(v_a_4632_);
lean_inc(v_a_4631_);
v___x_4643_ = lean_grind_process_to_do(v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
return v___x_4643_;
}
else
{
return v___x_4642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4644_, lean_object* v_rhs_4645_, lean_object* v_proof_4646_, lean_object* v_isHEq_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
uint8_t v_isHEq_boxed_4659_; lean_object* v_res_4660_; 
v_isHEq_boxed_4659_ = lean_unbox(v_isHEq_4647_);
v_res_4660_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4644_, v_rhs_4645_, v_proof_4646_, v_isHEq_boxed_4659_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec(v_a_4648_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4661_, lean_object* v_rhs_4662_, lean_object* v_proof_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
uint8_t v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = 0;
v___x_4676_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4661_, v_rhs_4662_, v_proof_4663_, v___x_4675_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4677_, lean_object* v_rhs_4678_, lean_object* v_proof_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4677_, v_rhs_4678_, v_proof_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec_ref(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_a_4684_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec(v_a_4680_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4692_, lean_object* v_rhs_4693_, lean_object* v_proof_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
uint8_t v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = 1;
v___x_4707_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4692_, v_rhs_4693_, v_proof_4694_, v___x_4706_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4708_, lean_object* v_rhs_4709_, lean_object* v_proof_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4708_, v_rhs_4709_, v_proof_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
lean_dec(v_a_4716_);
lean_dec_ref(v_a_4715_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec(v_a_4711_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4723_, lean_object* v_a_4724_){
_start:
{
lean_object* v___x_4726_; lean_object* v_toGoalState_4727_; lean_object* v_mvarId_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4768_; 
v___x_4726_ = lean_st_ref_take(v_a_4724_);
v_toGoalState_4727_ = lean_ctor_get(v___x_4726_, 0);
v_mvarId_4728_ = lean_ctor_get(v___x_4726_, 1);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4730_ = v___x_4726_;
v_isShared_4731_ = v_isSharedCheck_4768_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_mvarId_4728_);
lean_inc(v_toGoalState_4727_);
lean_dec(v___x_4726_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4768_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v_nextDeclIdx_4732_; lean_object* v_enodeMap_4733_; lean_object* v_exprs_4734_; lean_object* v_parents_4735_; lean_object* v_congrTable_4736_; lean_object* v_appMap_4737_; lean_object* v_indicesFound_4738_; lean_object* v_toProcess_4739_; lean_object* v_internalizing_4740_; uint8_t v_inconsistent_4741_; lean_object* v_nextIdx_4742_; lean_object* v_newRawFacts_4743_; lean_object* v_facts_4744_; lean_object* v_extThms_4745_; lean_object* v_ematch_4746_; lean_object* v_inj_4747_; lean_object* v_split_4748_; lean_object* v_clean_4749_; lean_object* v_sstates_4750_; lean_object* v_goalStack_4751_; uint64_t v_introBase_4752_; lean_object* v_numIntros_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4767_; 
v_nextDeclIdx_4732_ = lean_ctor_get(v_toGoalState_4727_, 0);
v_enodeMap_4733_ = lean_ctor_get(v_toGoalState_4727_, 1);
v_exprs_4734_ = lean_ctor_get(v_toGoalState_4727_, 2);
v_parents_4735_ = lean_ctor_get(v_toGoalState_4727_, 3);
v_congrTable_4736_ = lean_ctor_get(v_toGoalState_4727_, 4);
v_appMap_4737_ = lean_ctor_get(v_toGoalState_4727_, 5);
v_indicesFound_4738_ = lean_ctor_get(v_toGoalState_4727_, 6);
v_toProcess_4739_ = lean_ctor_get(v_toGoalState_4727_, 7);
v_internalizing_4740_ = lean_ctor_get(v_toGoalState_4727_, 8);
v_inconsistent_4741_ = lean_ctor_get_uint8(v_toGoalState_4727_, sizeof(void*)*20 + 8);
v_nextIdx_4742_ = lean_ctor_get(v_toGoalState_4727_, 9);
v_newRawFacts_4743_ = lean_ctor_get(v_toGoalState_4727_, 10);
v_facts_4744_ = lean_ctor_get(v_toGoalState_4727_, 11);
v_extThms_4745_ = lean_ctor_get(v_toGoalState_4727_, 12);
v_ematch_4746_ = lean_ctor_get(v_toGoalState_4727_, 13);
v_inj_4747_ = lean_ctor_get(v_toGoalState_4727_, 14);
v_split_4748_ = lean_ctor_get(v_toGoalState_4727_, 15);
v_clean_4749_ = lean_ctor_get(v_toGoalState_4727_, 16);
v_sstates_4750_ = lean_ctor_get(v_toGoalState_4727_, 17);
v_goalStack_4751_ = lean_ctor_get(v_toGoalState_4727_, 18);
v_introBase_4752_ = lean_ctor_get_uint64(v_toGoalState_4727_, sizeof(void*)*20);
v_numIntros_4753_ = lean_ctor_get(v_toGoalState_4727_, 19);
v_isSharedCheck_4767_ = !lean_is_exclusive(v_toGoalState_4727_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4755_ = v_toGoalState_4727_;
v_isShared_4756_ = v_isSharedCheck_4767_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_numIntros_4753_);
lean_inc(v_goalStack_4751_);
lean_inc(v_sstates_4750_);
lean_inc(v_clean_4749_);
lean_inc(v_split_4748_);
lean_inc(v_inj_4747_);
lean_inc(v_ematch_4746_);
lean_inc(v_extThms_4745_);
lean_inc(v_facts_4744_);
lean_inc(v_newRawFacts_4743_);
lean_inc(v_nextIdx_4742_);
lean_inc(v_internalizing_4740_);
lean_inc(v_toProcess_4739_);
lean_inc(v_indicesFound_4738_);
lean_inc(v_appMap_4737_);
lean_inc(v_congrTable_4736_);
lean_inc(v_parents_4735_);
lean_inc(v_exprs_4734_);
lean_inc(v_enodeMap_4733_);
lean_inc(v_nextDeclIdx_4732_);
lean_dec(v_toGoalState_4727_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4767_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4757_ = lean_box(0);
v___x_4758_ = l_Lean_PersistentArray_push___redArg(v_facts_4744_, v_fact_4723_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 11, v___x_4758_);
v___x_4760_ = v___x_4755_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 20, 9);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_nextDeclIdx_4732_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v_enodeMap_4733_);
lean_ctor_set(v_reuseFailAlloc_4766_, 2, v_exprs_4734_);
lean_ctor_set(v_reuseFailAlloc_4766_, 3, v_parents_4735_);
lean_ctor_set(v_reuseFailAlloc_4766_, 4, v_congrTable_4736_);
lean_ctor_set(v_reuseFailAlloc_4766_, 5, v_appMap_4737_);
lean_ctor_set(v_reuseFailAlloc_4766_, 6, v_indicesFound_4738_);
lean_ctor_set(v_reuseFailAlloc_4766_, 7, v_toProcess_4739_);
lean_ctor_set(v_reuseFailAlloc_4766_, 8, v_internalizing_4740_);
lean_ctor_set(v_reuseFailAlloc_4766_, 9, v_nextIdx_4742_);
lean_ctor_set(v_reuseFailAlloc_4766_, 10, v_newRawFacts_4743_);
lean_ctor_set(v_reuseFailAlloc_4766_, 11, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4766_, 12, v_extThms_4745_);
lean_ctor_set(v_reuseFailAlloc_4766_, 13, v_ematch_4746_);
lean_ctor_set(v_reuseFailAlloc_4766_, 14, v_inj_4747_);
lean_ctor_set(v_reuseFailAlloc_4766_, 15, v_split_4748_);
lean_ctor_set(v_reuseFailAlloc_4766_, 16, v_clean_4749_);
lean_ctor_set(v_reuseFailAlloc_4766_, 17, v_sstates_4750_);
lean_ctor_set(v_reuseFailAlloc_4766_, 18, v_goalStack_4751_);
lean_ctor_set(v_reuseFailAlloc_4766_, 19, v_numIntros_4753_);
lean_ctor_set_uint8(v_reuseFailAlloc_4766_, sizeof(void*)*20 + 8, v_inconsistent_4741_);
lean_ctor_set_uint64(v_reuseFailAlloc_4766_, sizeof(void*)*20, v_introBase_4752_);
v___x_4760_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v___x_4760_);
v___x_4762_ = v___x_4730_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_mvarId_4728_);
v___x_4762_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_st_ref_put(v_a_4724_, v___x_4762_);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4757_);
return v___x_4764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4769_, v_a_4770_);
lean_dec(v_a_4770_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4773_, v_a_4774_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
lean_dec(v_a_4790_);
lean_dec_ref(v_a_4789_);
lean_dec(v_a_4788_);
lean_dec(v_a_4787_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4799_, lean_object* v_rhs_4800_, lean_object* v_proof_4801_, lean_object* v_generation_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v___x_4814_; 
lean_inc_ref(v_rhs_4800_);
lean_inc_ref(v_lhs_4799_);
v___x_4814_ = l_Lean_Meta_mkEq(v_lhs_4799_, v_rhs_4800_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4826_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc_n(v_a_4815_, 2);
lean_dec_ref_known(v___x_4814_, 1);
v___x_4816_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4815_, v_a_4803_);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4826_ == 0)
{
lean_object* v_unused_4827_; 
v_unused_4827_ = lean_ctor_get(v___x_4816_, 0);
lean_dec(v_unused_4827_);
v___x_4818_ = v___x_4816_;
v_isShared_4819_ = v_isSharedCheck_4826_;
goto v_resetjp_4817_;
}
else
{
lean_dec(v___x_4816_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4826_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
lean_ctor_set_tag(v___x_4818_, 1);
lean_ctor_set(v___x_4818_, 0, v_a_4815_);
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4815_);
v___x_4821_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
lean_object* v___x_4822_; 
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc_ref(v_a_4809_);
lean_inc(v_a_4808_);
lean_inc_ref(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc_ref(v_a_4805_);
lean_inc(v_a_4804_);
lean_inc(v_a_4803_);
lean_inc_ref(v___x_4821_);
lean_inc(v_generation_4802_);
lean_inc_ref(v_lhs_4799_);
v___x_4822_ = lean_grind_internalize(v_lhs_4799_, v_generation_4802_, v___x_4821_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v___x_4823_; 
lean_dec_ref_known(v___x_4822_, 1);
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc_ref(v_a_4809_);
lean_inc(v_a_4808_);
lean_inc_ref(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc_ref(v_a_4805_);
lean_inc(v_a_4804_);
lean_inc(v_a_4803_);
lean_inc_ref(v_rhs_4800_);
v___x_4823_ = lean_grind_internalize(v_rhs_4800_, v_generation_4802_, v___x_4821_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v___x_4824_; 
lean_dec_ref_known(v___x_4823_, 1);
v___x_4824_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4799_, v_rhs_4800_, v_proof_4801_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
return v___x_4824_;
}
else
{
lean_dec_ref(v_proof_4801_);
lean_dec_ref(v_rhs_4800_);
lean_dec_ref(v_lhs_4799_);
return v___x_4823_;
}
}
else
{
lean_dec_ref(v___x_4821_);
lean_dec(v_generation_4802_);
lean_dec_ref(v_proof_4801_);
lean_dec_ref(v_rhs_4800_);
lean_dec_ref(v_lhs_4799_);
return v___x_4822_;
}
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec(v_generation_4802_);
lean_dec_ref(v_proof_4801_);
lean_dec_ref(v_rhs_4800_);
lean_dec_ref(v_lhs_4799_);
v_a_4828_ = lean_ctor_get(v___x_4814_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4814_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4814_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4836_, lean_object* v_rhs_4837_, lean_object* v_proof_4838_, lean_object* v_generation_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4836_, v_rhs_4837_, v_proof_4838_, v_generation_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec(v_a_4840_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4852_, lean_object* v_generation_4853_, lean_object* v_p_4854_, uint8_t v_isNeg_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = lean_box(0);
lean_inc(v_a_4865_);
lean_inc_ref(v_a_4864_);
lean_inc(v_a_4863_);
lean_inc_ref(v_a_4862_);
lean_inc(v_a_4861_);
lean_inc_ref(v_a_4860_);
lean_inc(v_a_4859_);
lean_inc_ref(v_a_4858_);
lean_inc(v_a_4857_);
lean_inc(v_a_4856_);
lean_inc_ref(v_p_4854_);
v___x_4868_ = lean_grind_internalize(v_p_4854_, v_generation_4853_, v___x_4867_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_dec_ref_known(v___x_4868_, 1);
if (v_isNeg_4855_ == 0)
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4860_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4871_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v___x_4871_ = l_Lean_Meta_mkEqTrue(v_proof_4852_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4873_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4871_, 1);
v___x_4873_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4854_, v_a_4870_, v_a_4872_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
return v___x_4873_;
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec(v_a_4870_);
lean_dec_ref(v_p_4854_);
v_a_4874_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4871_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4871_);
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
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
lean_dec_ref(v_p_4854_);
lean_dec_ref(v_proof_4852_);
v_a_4882_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4869_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4869_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
lean_object* v___x_4890_; 
v___x_4890_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4860_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4892_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v___x_4892_ = l_Lean_Meta_mkEqFalse(v_proof_4852_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4894_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4894_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4854_, v_a_4891_, v_a_4893_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
return v___x_4894_;
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v_a_4891_);
lean_dec_ref(v_p_4854_);
v_a_4895_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4892_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4892_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec_ref(v_p_4854_);
lean_dec_ref(v_proof_4852_);
v_a_4903_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4890_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4890_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4854_);
lean_dec_ref(v_proof_4852_);
return v___x_4868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4911_, lean_object* v_generation_4912_, lean_object* v_p_4913_, lean_object* v_isNeg_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
uint8_t v_isNeg_boxed_4926_; lean_object* v_res_4927_; 
v_isNeg_boxed_4926_ = lean_unbox(v_isNeg_4914_);
v_res_4927_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4911_, v_generation_4912_, v_p_4913_, v_isNeg_boxed_4926_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec_ref(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_a_4916_);
lean_dec(v_a_4915_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4928_, lean_object* v_generation_4929_, lean_object* v_p_4930_, lean_object* v_lhs_4931_, lean_object* v_rhs_4932_, uint8_t v_isNeg_4933_, uint8_t v_isHEq_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
if (v_isNeg_4933_ == 0)
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
lean_inc_ref(v_p_4930_);
v___x_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_p_4930_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc_ref(v_a_4937_);
lean_inc(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v___x_4946_);
lean_inc(v_generation_4929_);
lean_inc_ref(v_lhs_4931_);
v___x_4947_ = lean_grind_internalize(v_lhs_4931_, v_generation_4929_, v___x_4946_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_object* v___x_4948_; 
lean_dec_ref_known(v___x_4947_, 1);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc_ref(v_a_4937_);
lean_inc(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v_rhs_4932_);
v___x_4948_ = lean_grind_internalize(v_rhs_4932_, v_generation_4929_, v___x_4946_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4948_) == 0)
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_dec_ref_known(v___x_4948_, 1);
v___x_4949_ = lean_box(0);
v___x_4950_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4930_, v___x_4949_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4951_; 
lean_dec_ref_known(v___x_4950_, 1);
v___x_4951_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4931_, v_rhs_4932_, v_proof_4928_, v_isHEq_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v___x_4951_;
}
else
{
lean_dec_ref(v_rhs_4932_);
lean_dec_ref(v_lhs_4931_);
lean_dec_ref(v_proof_4928_);
return v___x_4950_;
}
}
else
{
lean_dec_ref(v_rhs_4932_);
lean_dec_ref(v_lhs_4931_);
lean_dec_ref(v_p_4930_);
lean_dec_ref(v_proof_4928_);
return v___x_4948_;
}
}
else
{
lean_dec_ref_known(v___x_4946_, 1);
lean_dec_ref(v_rhs_4932_);
lean_dec_ref(v_lhs_4931_);
lean_dec_ref(v_p_4930_);
lean_dec(v_generation_4929_);
lean_dec_ref(v_proof_4928_);
return v___x_4947_;
}
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref(v_rhs_4932_);
lean_dec_ref(v_lhs_4931_);
v___x_4952_ = lean_box(0);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc_ref(v_a_4937_);
lean_inc(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v_p_4930_);
v___x_4953_ = lean_grind_internalize(v_p_4930_, v_generation_4929_, v___x_4952_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4953_, 1);
v___x_4954_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4939_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; lean_object* v___x_4956_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v___x_4956_ = l_Lean_Meta_mkEqFalse(v_proof_4928_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4958_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v___x_4958_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4930_, v_a_4955_, v_a_4957_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v___x_4958_;
}
else
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v_a_4955_);
lean_dec_ref(v_p_4930_);
v_a_4959_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4956_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4956_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec_ref(v_p_4930_);
lean_dec_ref(v_proof_4928_);
v_a_4967_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4954_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4954_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
else
{
lean_dec_ref(v_p_4930_);
lean_dec_ref(v_proof_4928_);
return v___x_4953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4975_ = _args[0];
lean_object* v_generation_4976_ = _args[1];
lean_object* v_p_4977_ = _args[2];
lean_object* v_lhs_4978_ = _args[3];
lean_object* v_rhs_4979_ = _args[4];
lean_object* v_isNeg_4980_ = _args[5];
lean_object* v_isHEq_4981_ = _args[6];
lean_object* v_a_4982_ = _args[7];
lean_object* v_a_4983_ = _args[8];
lean_object* v_a_4984_ = _args[9];
lean_object* v_a_4985_ = _args[10];
lean_object* v_a_4986_ = _args[11];
lean_object* v_a_4987_ = _args[12];
lean_object* v_a_4988_ = _args[13];
lean_object* v_a_4989_ = _args[14];
lean_object* v_a_4990_ = _args[15];
lean_object* v_a_4991_ = _args[16];
lean_object* v_a_4992_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4993_; uint8_t v_isHEq_boxed_4994_; lean_object* v_res_4995_; 
v_isNeg_boxed_4993_ = lean_unbox(v_isNeg_4980_);
v_isHEq_boxed_4994_ = lean_unbox(v_isHEq_4981_);
v_res_4995_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4975_, v_generation_4976_, v_p_4977_, v_lhs_4978_, v_rhs_4979_, v_isNeg_boxed_4993_, v_isHEq_boxed_4994_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
lean_dec(v_a_4985_);
lean_dec_ref(v_a_4984_);
lean_dec(v_a_4983_);
lean_dec(v_a_4982_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4999_, lean_object* v_generation_5000_, lean_object* v_p_5001_, uint8_t v_isNeg_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v___x_5014_; 
lean_inc_ref(v_p_5001_);
v___x_5014_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_5001_, v_a_5010_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
v___x_5016_ = l_Lean_Expr_cleanupAnnotations(v_a_5015_);
lean_dec(v_a_5015_);
v___x_5017_ = l_Lean_Expr_isApp(v___x_5016_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; 
lean_dec_ref(v___x_5016_);
v___x_5018_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5018_;
}
else
{
lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5016_);
v___x_5020_ = l_Lean_Expr_isApp(v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec_ref(v___x_5019_);
lean_dec_ref(v___x_5016_);
v___x_5021_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5019_);
v___x_5023_ = l_Lean_Expr_isApp(v___x_5022_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; 
lean_dec_ref(v___x_5022_);
lean_dec_ref(v___x_5019_);
lean_dec_ref(v___x_5016_);
v___x_5024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5024_;
}
else
{
lean_object* v_arg_5025_; lean_object* v_arg_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; 
v_arg_5025_ = lean_ctor_get(v___x_5016_, 1);
lean_inc_ref(v_arg_5025_);
lean_dec_ref(v___x_5016_);
v_arg_5026_ = lean_ctor_get(v___x_5022_, 1);
lean_inc_ref(v_arg_5026_);
v___x_5027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5022_);
lean_dec_ref(v___x_5022_);
v___x_5028_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5029_ = l_Lean_Expr_isConstOf(v___x_5027_, v___x_5028_);
if (v___x_5029_ == 0)
{
uint8_t v___x_5030_; 
lean_dec_ref(v___x_5019_);
v___x_5030_ = l_Lean_Expr_isApp(v___x_5027_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; 
lean_dec_ref(v___x_5027_);
lean_dec_ref(v_arg_5026_);
lean_dec_ref(v_arg_5025_);
v___x_5031_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5031_;
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; uint8_t v___x_5034_; 
v___x_5032_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5027_);
lean_dec_ref(v___x_5027_);
v___x_5033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5034_ = l_Lean_Expr_isConstOf(v___x_5032_, v___x_5033_);
lean_dec_ref(v___x_5032_);
if (v___x_5034_ == 0)
{
lean_object* v___x_5035_; 
lean_dec_ref(v_arg_5026_);
lean_dec_ref(v_arg_5025_);
v___x_5035_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5035_;
}
else
{
lean_object* v___x_5036_; 
v___x_5036_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4999_, v_generation_5000_, v_p_5001_, v_arg_5026_, v_arg_5025_, v_isNeg_5002_, v___x_5034_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5036_;
}
}
}
else
{
uint8_t v___x_5037_; 
lean_dec_ref(v___x_5027_);
v___x_5037_ = l_Lean_Expr_isProp(v_arg_5026_);
lean_dec_ref(v_arg_5026_);
if (v___x_5037_ == 0)
{
lean_object* v_arg_5038_; lean_object* v___x_5039_; 
v_arg_5038_ = lean_ctor_get(v___x_5019_, 1);
lean_inc_ref(v_arg_5038_);
lean_dec_ref(v___x_5019_);
v___x_5039_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4999_, v_generation_5000_, v_p_5001_, v_arg_5038_, v_arg_5025_, v_isNeg_5002_, v___x_5037_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5039_;
}
else
{
lean_object* v___x_5040_; 
lean_dec_ref(v_arg_5025_);
lean_dec_ref(v___x_5019_);
v___x_5040_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4999_, v_generation_5000_, v_p_5001_, v_isNeg_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5040_;
}
}
}
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec_ref(v_p_5001_);
lean_dec(v_generation_5000_);
lean_dec_ref(v_proof_4999_);
v_a_5041_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_5014_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5014_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5049_, lean_object* v_generation_5050_, lean_object* v_p_5051_, lean_object* v_isNeg_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_){
_start:
{
uint8_t v_isNeg_boxed_5064_; lean_object* v_res_5065_; 
v_isNeg_boxed_5064_ = lean_unbox(v_isNeg_5052_);
v_res_5065_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5049_, v_generation_5050_, v_p_5051_, v_isNeg_boxed_5064_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec(v_a_5053_);
return v_res_5065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5074_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5075_ = l_Lean_Name_append(v___x_5074_, v___x_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5076_, lean_object* v_proof_5077_, lean_object* v_generation_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_){
_start:
{
lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___x_5121_; lean_object* v_toCold_5122_; lean_object* v_options_5123_; uint8_t v_hasTrace_5124_; 
lean_inc_ref(v_fact_5076_);
v___x_5121_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5076_, v_a_5079_);
lean_dec_ref(v___x_5121_);
v_toCold_5122_ = lean_ctor_get(v_a_5087_, 0);
v_options_5123_ = lean_ctor_get(v_toCold_5122_, 2);
v_hasTrace_5124_ = lean_ctor_get_uint8(v_options_5123_, sizeof(void*)*1);
if (v_hasTrace_5124_ == 0)
{
v___y_5104_ = v_a_5079_;
v___y_5105_ = v_a_5080_;
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
goto v___jp_5103_;
}
else
{
lean_object* v_inheritedTraceOptions_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; uint8_t v___x_5128_; 
v_inheritedTraceOptions_5125_ = lean_ctor_get(v_toCold_5122_, 11);
v___x_5126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5128_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5125_, v_options_5123_, v___x_5127_);
if (v___x_5128_ == 0)
{
v___y_5104_ = v_a_5079_;
v___y_5105_ = v_a_5080_;
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
goto v___jp_5103_;
}
else
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_Meta_Grind_updateLastTag(v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_dec_ref_known(v___x_5129_, 1);
lean_inc_ref(v_fact_5076_);
v___x_5130_ = l_Lean_MessageData_ofExpr(v_fact_5076_);
v___x_5131_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5126_, v___x_5130_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_dec_ref_known(v___x_5131_, 1);
v___y_5104_ = v_a_5079_;
v___y_5105_ = v_a_5080_;
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
goto v___jp_5103_;
}
else
{
lean_dec(v_generation_5078_);
lean_dec_ref(v_proof_5077_);
lean_dec_ref(v_fact_5076_);
return v___x_5131_;
}
}
else
{
lean_dec(v_generation_5078_);
lean_dec_ref(v_proof_5077_);
lean_dec_ref(v_fact_5076_);
return v___x_5129_;
}
}
}
v___jp_5090_:
{
uint8_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = 0;
v___x_5102_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5077_, v_generation_5078_, v_fact_5076_, v___x_5101_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
return v___x_5102_;
}
v___jp_5103_:
{
lean_object* v___x_5114_; uint8_t v___x_5115_; 
v___x_5114_ = l_Lean_Expr_cleanupAnnotations(v_fact_5076_);
v___x_5115_ = l_Lean_Expr_isApp(v___x_5114_);
if (v___x_5115_ == 0)
{
lean_dec_ref(v___x_5114_);
v___y_5091_ = v___y_5104_;
v___y_5092_ = v___y_5105_;
v___y_5093_ = v___y_5106_;
v___y_5094_ = v___y_5107_;
v___y_5095_ = v___y_5108_;
v___y_5096_ = v___y_5109_;
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
goto v___jp_5090_;
}
else
{
lean_object* v___x_5116_; lean_object* v___x_5117_; uint8_t v___x_5118_; 
v___x_5116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5114_);
v___x_5117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5118_ = l_Lean_Expr_isConstOf(v___x_5116_, v___x_5117_);
lean_dec_ref(v___x_5116_);
if (v___x_5118_ == 0)
{
lean_dec_ref(v___x_5114_);
v___y_5091_ = v___y_5104_;
v___y_5092_ = v___y_5105_;
v___y_5093_ = v___y_5106_;
v___y_5094_ = v___y_5107_;
v___y_5095_ = v___y_5108_;
v___y_5096_ = v___y_5109_;
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
goto v___jp_5090_;
}
else
{
lean_object* v_arg_5119_; lean_object* v___x_5120_; 
lean_dec_ref(v_fact_5076_);
v_arg_5119_ = lean_ctor_get(v___x_5114_, 1);
lean_inc_ref(v_arg_5119_);
lean_dec_ref(v___x_5114_);
v___x_5120_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5077_, v_generation_5078_, v_arg_5119_, v___x_5118_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
return v___x_5120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5132_, lean_object* v_proof_5133_, lean_object* v_generation_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_){
_start:
{
lean_object* v_res_5146_; 
v_res_5146_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5132_, v_proof_5133_, v_generation_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_);
lean_dec(v_a_5144_);
lean_dec_ref(v_a_5143_);
lean_dec(v_a_5142_);
lean_dec_ref(v_a_5141_);
lean_dec(v_a_5140_);
lean_dec_ref(v_a_5139_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec(v_a_5135_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5150_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; uint8_t v___x_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5163_ = lean_unbox(v_a_5162_);
lean_dec(v_a_5162_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5164_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5165_ = l_Lean_Core_checkSystem(v___x_5164_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v___x_5166_; 
lean_dec_ref_known(v___x_5165_, 1);
v___x_5166_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5150_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5240_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5169_ = v___x_5166_;
v_isShared_5170_ = v_isSharedCheck_5240_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5166_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5240_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
if (lean_obj_tag(v_a_5167_) == 1)
{
lean_object* v_val_5171_; 
lean_del_object(v___x_5169_);
v_val_5171_ = lean_ctor_get(v_a_5167_, 0);
lean_inc(v_val_5171_);
lean_dec_ref_known(v_a_5167_, 1);
switch(lean_obj_tag(v_val_5171_))
{
case 0:
{
lean_object* v_lhs_5172_; lean_object* v_rhs_5173_; lean_object* v_proof_5174_; uint8_t v_isHEq_5175_; lean_object* v___x_5176_; 
v_lhs_5172_ = lean_ctor_get(v_val_5171_, 0);
lean_inc_ref(v_lhs_5172_);
v_rhs_5173_ = lean_ctor_get(v_val_5171_, 1);
lean_inc_ref(v_rhs_5173_);
v_proof_5174_ = lean_ctor_get(v_val_5171_, 2);
lean_inc_ref(v_proof_5174_);
v_isHEq_5175_ = lean_ctor_get_uint8(v_val_5171_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5171_, 3);
v___x_5176_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5172_, v_rhs_5173_, v_proof_5174_, v_isHEq_5175_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_dec_ref_known(v___x_5176_, 1);
goto _start;
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
v_a_5178_ = lean_ctor_get(v___x_5176_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5176_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5176_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5176_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
case 1:
{
lean_object* v_prop_5186_; lean_object* v_proof_5187_; lean_object* v_generation_5188_; lean_object* v___x_5189_; 
v_prop_5186_ = lean_ctor_get(v_val_5171_, 0);
lean_inc_ref(v_prop_5186_);
v_proof_5187_ = lean_ctor_get(v_val_5171_, 1);
lean_inc_ref(v_proof_5187_);
v_generation_5188_ = lean_ctor_get(v_val_5171_, 2);
lean_inc(v_generation_5188_);
lean_dec_ref_known(v_val_5171_, 3);
v___x_5189_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5186_, v_proof_5187_, v_generation_5188_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_dec_ref_known(v___x_5189_, 1);
goto _start;
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
v_a_5191_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_5189_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___x_5189_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
case 2:
{
lean_object* v_e_5199_; lean_object* v___x_5200_; 
v_e_5199_ = lean_ctor_get(v_val_5171_, 0);
lean_inc_ref(v_e_5199_);
lean_dec_ref_known(v_val_5171_, 1);
v___x_5200_ = l_Lean_Meta_Grind_propagateUp(v_e_5199_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_dec_ref_known(v___x_5200_, 1);
goto _start;
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
v_a_5202_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5200_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5200_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
case 3:
{
lean_object* v_solverId_5210_; lean_object* v_lhs_5211_; lean_object* v_rhs_5212_; lean_object* v___x_5213_; 
v_solverId_5210_ = lean_ctor_get(v_val_5171_, 0);
lean_inc(v_solverId_5210_);
v_lhs_5211_ = lean_ctor_get(v_val_5171_, 1);
lean_inc_ref(v_lhs_5211_);
v_rhs_5212_ = lean_ctor_get(v_val_5171_, 2);
lean_inc_ref(v_rhs_5212_);
lean_dec_ref_known(v_val_5171_, 3);
v___x_5213_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5210_, v_lhs_5211_, v_rhs_5212_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
lean_dec(v_solverId_5210_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_dec_ref_known(v___x_5213_, 1);
goto _start;
}
else
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
v_a_5215_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5213_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5213_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
default: 
{
lean_object* v_solverId_5223_; lean_object* v_lhs_5224_; lean_object* v_rhs_5225_; lean_object* v___x_5226_; 
v_solverId_5223_ = lean_ctor_get(v_val_5171_, 0);
lean_inc(v_solverId_5223_);
v_lhs_5224_ = lean_ctor_get(v_val_5171_, 1);
lean_inc_ref(v_lhs_5224_);
v_rhs_5225_ = lean_ctor_get(v_val_5171_, 2);
lean_inc_ref(v_rhs_5225_);
lean_dec_ref_known(v_val_5171_, 3);
v___x_5226_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5223_, v_lhs_5224_, v_rhs_5225_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
lean_dec(v_solverId_5223_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_dec_ref_known(v___x_5226_, 1);
goto _start;
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
v_a_5228_ = lean_ctor_get(v___x_5226_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5226_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5226_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5226_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
}
}
else
{
lean_object* v___x_5236_; lean_object* v___x_5238_; 
lean_dec(v_a_5167_);
v___x_5236_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5170_ == 0)
{
lean_ctor_set(v___x_5169_, 0, v___x_5236_);
v___x_5238_ = v___x_5169_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
v_a_5241_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5243_ = v___x_5166_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5166_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5246_; 
if (v_isShared_5244_ == 0)
{
v___x_5246_ = v___x_5243_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
v_a_5249_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5165_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5165_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
}
else
{
lean_object* v___x_5257_; 
v___x_5257_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5150_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5265_; 
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; 
v_unused_5266_ = lean_ctor_get(v___x_5257_, 0);
lean_dec(v_unused_5266_);
v___x_5259_ = v___x_5257_;
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
else
{
lean_dec(v___x_5257_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5261_; lean_object* v___x_5263_; 
v___x_5261_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5261_);
v___x_5263_ = v___x_5259_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5261_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
v_a_5267_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5257_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5257_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5277_; uint8_t v_isShared_5278_; uint8_t v_isSharedCheck_5282_; 
v_a_5275_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5277_ = v___x_5161_;
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
else
{
lean_inc(v_a_5275_);
lean_dec(v___x_5161_);
v___x_5277_ = lean_box(0);
v_isShared_5278_ = v_isSharedCheck_5282_;
goto v_resetjp_5276_;
}
v_resetjp_5276_:
{
lean_object* v___x_5280_; 
if (v_isShared_5278_ == 0)
{
v___x_5280_ = v___x_5277_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5275_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec(v___y_5283_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = lean_box(0);
v___x_5307_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_);
lean_dec(v_a_5304_);
lean_dec_ref(v_a_5303_);
lean_dec(v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
lean_dec(v_a_5298_);
lean_dec_ref(v_a_5297_);
lean_dec(v_a_5296_);
lean_dec(v_a_5295_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5320_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5310_ = v___x_5307_;
v_isShared_5311_ = v_isSharedCheck_5320_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5307_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5320_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v_fst_5312_; 
v_fst_5312_ = lean_ctor_get(v_a_5308_, 0);
lean_inc(v_fst_5312_);
lean_dec(v_a_5308_);
if (lean_obj_tag(v_fst_5312_) == 0)
{
lean_object* v___x_5314_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 0, v___x_5306_);
v___x_5314_ = v___x_5310_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5306_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
else
{
lean_object* v_val_5316_; lean_object* v___x_5318_; 
v_val_5316_ = lean_ctor_get(v_fst_5312_, 0);
lean_inc(v_val_5316_);
lean_dec_ref_known(v_fst_5312_, 1);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 0, v_val_5316_);
v___x_5318_ = v___x_5310_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_val_5316_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
v_a_5321_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5307_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5307_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = lean_grind_process_to_do(v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5341_, lean_object* v_a_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v___x_5354_; 
v___x_5354_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5355_, lean_object* v_a_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5355_, v_a_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v_a_5356_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5369_, lean_object* v_proof_5370_, lean_object* v_generation_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
uint8_t v___x_5383_; 
v___x_5383_ = l_Lean_Expr_isTrue(v_fact_5369_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; 
v___x_5384_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5372_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5415_; 
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5387_ = v___x_5384_;
v_isShared_5388_ = v_isSharedCheck_5415_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5384_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5415_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
uint8_t v___x_5389_; 
v___x_5389_ = lean_unbox(v_a_5385_);
lean_dec(v_a_5385_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5390_; 
lean_del_object(v___x_5387_);
lean_inc(v_a_5381_);
lean_inc_ref(v_a_5380_);
lean_inc(v_a_5379_);
lean_inc_ref(v_a_5378_);
lean_inc(v_a_5377_);
lean_inc_ref(v_a_5376_);
lean_inc(v_a_5375_);
lean_inc_ref(v_a_5374_);
lean_inc(v_a_5373_);
lean_inc(v_a_5372_);
v___x_5390_ = lean_grind_process_to_do(v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v___x_5391_; 
lean_dec_ref_known(v___x_5390_, 1);
v___x_5391_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5372_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5402_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5394_ = v___x_5391_;
v_isShared_5395_ = v_isSharedCheck_5402_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5402_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
uint8_t v___x_5396_; 
v___x_5396_ = lean_unbox(v_a_5392_);
lean_dec(v_a_5392_);
if (v___x_5396_ == 0)
{
lean_object* v___x_5397_; 
lean_del_object(v___x_5394_);
v___x_5397_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5369_, v_proof_5370_, v_generation_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_);
return v___x_5397_;
}
else
{
lean_object* v___x_5398_; lean_object* v___x_5400_; 
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
v___x_5398_ = lean_box(0);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v___x_5398_);
v___x_5400_ = v___x_5394_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
v_a_5403_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5391_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5391_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
else
{
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
return v___x_5390_;
}
}
else
{
lean_object* v___x_5411_; lean_object* v___x_5413_; 
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
v___x_5411_ = lean_box(0);
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 0, v___x_5411_);
v___x_5413_ = v___x_5387_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
v_a_5416_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5384_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5384_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
else
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
lean_dec(v_generation_5371_);
lean_dec_ref(v_proof_5370_);
lean_dec_ref(v_fact_5369_);
v___x_5424_ = lean_box(0);
v___x_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
return v___x_5425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5426_, lean_object* v_proof_5427_, lean_object* v_generation_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Lean_Meta_Grind_add(v_fact_5426_, v_proof_5427_, v_generation_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_);
lean_dec(v_a_5438_);
lean_dec_ref(v_a_5437_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
lean_dec(v_a_5430_);
lean_dec(v_a_5429_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5441_, lean_object* v_generation_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_){
_start:
{
lean_object* v___x_5454_; 
lean_inc(v_fvarId_5441_);
v___x_5454_ = l_Lean_FVarId_getType___redArg(v_fvarId_5441_, v_a_5449_, v_a_5451_, v_a_5452_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = l_Lean_mkFVar(v_fvarId_5441_);
v___x_5457_ = l_Lean_Meta_Grind_add(v_a_5455_, v___x_5456_, v_generation_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_);
return v___x_5457_;
}
else
{
lean_object* v_a_5458_; lean_object* v___x_5460_; uint8_t v_isShared_5461_; uint8_t v_isSharedCheck_5465_; 
lean_dec(v_generation_5442_);
lean_dec(v_fvarId_5441_);
v_a_5458_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5465_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5465_ == 0)
{
v___x_5460_ = v___x_5454_;
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
else
{
lean_inc(v_a_5458_);
lean_dec(v___x_5454_);
v___x_5460_ = lean_box(0);
v_isShared_5461_ = v_isSharedCheck_5465_;
goto v_resetjp_5459_;
}
v_resetjp_5459_:
{
lean_object* v___x_5463_; 
if (v_isShared_5461_ == 0)
{
v___x_5463_ = v___x_5460_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5466_, lean_object* v_generation_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_){
_start:
{
lean_object* v_res_5479_; 
v_res_5479_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5466_, v_generation_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_);
lean_dec(v_a_5477_);
lean_dec_ref(v_a_5476_);
lean_dec(v_a_5475_);
lean_dec_ref(v_a_5474_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
lean_dec(v_a_5471_);
lean_dec_ref(v_a_5470_);
lean_dec(v_a_5469_);
lean_dec(v_a_5468_);
return v_res_5479_;
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
