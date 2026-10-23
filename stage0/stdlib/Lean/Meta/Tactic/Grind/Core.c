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
size_t v_x_22821__boxed_357_; lean_object* v_res_358_; 
v_x_22821__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_22821__boxed_357_, v_x_356_);
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
size_t v_x_23281__boxed_610_; lean_object* v_res_611_; 
v_x_23281__boxed_610_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_res_611_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_605_, v_00_u03b2_606_, v_x_607_, v_x_23281__boxed_610_, v_x_609_);
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
lean_dec_ref_known(v_snd_1228_, 2);
lean_dec_ref(v_fn_1246_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2027_, lean_object* v_as_2028_, size_t v_sz_2029_, size_t v_i_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_a_2044_; uint8_t v___x_2048_; 
v___x_2048_ = lean_usize_dec_lt(v_i_2030_, v_sz_2029_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2031_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; lean_object* v_a_2051_; 
v___x_2050_ = lean_box(0);
v_a_2051_ = lean_array_uget_borrowed(v_as_2028_, v_i_2030_);
if (lean_obj_tag(v_a_2051_) == 6)
{
lean_object* v_binderType_2052_; lean_object* v_body_2053_; lean_object* v___x_2054_; 
v_binderType_2052_ = lean_ctor_get(v_a_2051_, 1);
v_body_2053_ = lean_ctor_get(v_a_2051_, 2);
lean_inc_ref(v_binderType_2052_);
v___x_2054_ = l_Lean_Meta_getLevel(v_binderType_2052_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2057_ = lean_box(0);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2055_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_inc_ref(v___x_2058_);
v___x_2059_ = l_Lean_mkConst(v___x_2056_, v___x_2058_);
lean_inc_ref(v_binderType_2052_);
v___x_2060_ = l_Lean_Expr_app___override(v___x_2059_, v_binderType_2052_);
v___x_2061_ = lean_box(0);
v___x_2062_ = l_Lean_Meta_synthInstance_x3f(v___x_2060_, v___x_2061_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
if (lean_obj_tag(v_a_2063_) == 1)
{
lean_object* v_val_2064_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; uint8_t v___x_2127_; 
v_val_2064_ = lean_ctor_get(v_a_2063_, 0);
lean_inc(v_val_2064_);
lean_dec_ref_known(v_a_2063_, 1);
v___x_2127_ = l_Lean_Expr_hasLooseBVars(v_body_2053_);
if (v___x_2127_ == 0)
{
v___y_2066_ = v___y_2032_;
v___y_2067_ = v___y_2033_;
v___y_2068_ = v___y_2034_;
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2058_);
v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2058_);
lean_inc_ref(v_binderType_2052_);
v___x_2130_ = l_Lean_Expr_app___override(v___x_2129_, v_binderType_2052_);
v___x_2131_ = l_Lean_Meta_synthInstance_x3f(v___x_2130_, v___x_2061_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
if (lean_obj_tag(v_a_2132_) == 0)
{
lean_dec(v_val_2064_);
lean_dec_ref_known(v___x_2058_, 2);
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
else
{
lean_dec_ref_known(v_a_2132_, 1);
v___y_2066_ = v___y_2032_;
v___y_2067_ = v___y_2033_;
v___y_2068_ = v___y_2034_;
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
goto v___jp_2065_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_val_2064_);
lean_dec_ref_known(v___x_2058_, 2);
v_a_2133_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2131_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
v___jp_2065_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2027_, v_binderType_2052_);
if (lean_obj_tag(v___x_2076_) == 1)
{
lean_object* v_val_2077_; 
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2076_, 1);
if (lean_obj_tag(v_val_2077_) == 6)
{
lean_object* v_body_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_body_2078_ = lean_ctor_get(v_val_2077_, 2);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2080_ = l_Lean_mkConst(v___x_2079_, v___x_2058_);
lean_inc_ref(v_binderType_2052_);
v___x_2081_ = l_Lean_mkAppB(v___x_2080_, v_binderType_2052_, v_val_2064_);
v___x_2082_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2081_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = lean_expr_instantiate1(v_body_2053_, v_a_2083_);
v___x_2085_ = lean_expr_instantiate1(v_body_2078_, v_a_2083_);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc_ref(v_a_2051_);
v___x_2086_ = lean_grind_mk_eq_proof(v_a_2051_, v_val_2077_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = l_Lean_Meta_mkCongrFun(v_a_2087_, v_a_2083_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = l_Lean_Meta_mkEq(v___x_2084_, v___x_2085_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Meta_mkExpectedPropHint(v_a_2089_, v_a_2091_);
v___x_2093_ = lean_unsigned_to_nat(0u);
v___x_2094_ = l_Lean_Meta_Grind_pushNewFact(v___x_2092_, v___x_2093_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
else
{
return v___x_2094_;
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2089_);
v_a_2095_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2090_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2090_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
v_a_2103_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2088_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2088_);
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
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_a_2083_);
v_a_2111_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2086_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2086_);
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
lean_dec_ref_known(v_val_2077_, 3);
v_a_2119_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2082_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2082_);
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
lean_dec(v_val_2077_);
lean_dec(v_val_2064_);
lean_dec_ref_known(v___x_2058_, 2);
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
}
else
{
lean_dec(v___x_2076_);
lean_dec(v_val_2064_);
lean_dec_ref_known(v___x_2058_, 2);
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
}
}
else
{
lean_dec(v_a_2063_);
lean_dec_ref_known(v___x_2058_, 2);
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref_known(v___x_2058_, 2);
v_a_2141_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2062_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2062_);
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
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_a_2149_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2054_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2054_);
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
v_a_2044_ = v___x_2050_;
goto v___jp_2043_;
}
}
v___jp_2043_:
{
size_t v___x_2045_; size_t v___x_2046_; 
v___x_2045_ = ((size_t)1ULL);
v___x_2046_ = lean_usize_add(v_i_2030_, v___x_2045_);
v_i_2030_ = v___x_2046_;
v_b_2031_ = v_a_2044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object* v_lams_u2082_2157_, lean_object* v_as_2158_, lean_object* v_sz_2159_, lean_object* v_i_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
size_t v_sz_boxed_2173_; size_t v_i_boxed_2174_; lean_object* v_res_2175_; 
v_sz_boxed_2173_ = lean_unbox_usize(v_sz_2159_);
lean_dec(v_sz_2159_);
v_i_boxed_2174_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2157_, v_as_2158_, v_sz_boxed_2173_, v_i_boxed_2174_, v_b_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v_as_2158_);
lean_dec_ref(v_lams_u2082_2157_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2176_, lean_object* v_lams_u2082_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_array_get_size(v_lams_u2081_2176_);
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_nat_dec_eq(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = lean_array_get_size(v_lams_u2082_2177_);
v___x_2196_ = lean_nat_dec_eq(v___x_2195_, v___x_2193_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; size_t v_sz_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = lean_box(0);
v_sz_2198_ = lean_array_size(v_lams_u2081_2176_);
v___x_2199_ = ((size_t)0ULL);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2177_, v_lams_u2081_2176_, v_sz_2198_, v___x_2199_, v___x_2197_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v___x_2200_, 0);
lean_dec(v_unused_2208_);
v___x_2202_ = v___x_2200_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2200_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2197_);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2197_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
return v___x_2200_;
}
}
else
{
goto v___jp_2189_;
}
}
else
{
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2209_, lean_object* v_lams_u2082_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2209_, v_lams_u2082_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_lams_u2082_2210_);
lean_dec_ref(v_lams_u2081_2209_);
return v_res_2222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2223_){
_start:
{
uint8_t v___x_2224_; 
v___x_2224_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2225_){
_start:
{
uint8_t v_res_2226_; lean_object* v_r_2227_; 
v_res_2226_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2225_);
lean_dec_ref(v_x_2225_);
v_r_2227_ = lean_box(v_res_2226_);
return v_r_2227_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2228_, lean_object* v_x_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_){
_start:
{
uint8_t v_res_2233_; lean_object* v_r_2234_; 
v_res_2233_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2231_, v_x_2232_);
lean_dec_ref(v_x_2232_);
v_r_2234_ = lean_box(v_res_2233_);
return v_r_2234_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2235_, lean_object* v_v_2236_, lean_object* v_i_2237_){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = lean_array_get_size(v_xs_2235_);
v___x_2239_ = lean_nat_dec_lt(v_i_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec(v_i_2237_);
v___x_2240_ = lean_box(0);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; size_t v___x_2242_; size_t v___x_2243_; uint8_t v___x_2244_; 
v___x_2241_ = lean_array_fget_borrowed(v_xs_2235_, v_i_2237_);
v___x_2242_ = lean_ptr_addr(v___x_2241_);
v___x_2243_ = lean_ptr_addr(v_v_2236_);
v___x_2244_ = lean_usize_dec_eq(v___x_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_i_2237_, v___x_2245_);
lean_dec(v_i_2237_);
v_i_2237_ = v___x_2246_;
goto _start;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_i_2237_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2249_, lean_object* v_v_2250_, lean_object* v_i_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2249_, v_v_2250_, v_i_2251_);
lean_dec_ref(v_v_2250_);
lean_dec_ref(v_xs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2253_, lean_object* v_v_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2253_, v_v_2254_, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2257_, lean_object* v_v_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2257_, v_v_2258_);
lean_dec_ref(v_v_2258_);
lean_dec_ref(v_xs_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2260_, size_t v_x_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v_es_2263_; lean_object* v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; lean_object* v_j_2267_; lean_object* v_entry_2268_; 
v_es_2263_ = lean_ctor_get(v_x_2260_, 0);
v___x_2264_ = lean_box(2);
v___x_2265_ = ((size_t)31ULL);
v___x_2266_ = lean_usize_land(v_x_2261_, v___x_2265_);
v_j_2267_ = lean_usize_to_nat(v___x_2266_);
v_entry_2268_ = lean_array_get(v___x_2264_, v_es_2263_, v_j_2267_);
switch(lean_obj_tag(v_entry_2268_))
{
case 0:
{
lean_object* v_key_2269_; size_t v___x_2270_; size_t v___x_2271_; uint8_t v___x_2272_; 
v_key_2269_ = lean_ctor_get(v_entry_2268_, 0);
lean_inc(v_key_2269_);
lean_dec_ref_known(v_entry_2268_, 2);
v___x_2270_ = lean_ptr_addr(v_x_2262_);
v___x_2271_ = lean_ptr_addr(v_key_2269_);
lean_dec(v_key_2269_);
v___x_2272_ = lean_usize_dec_eq(v___x_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v_j_2267_);
return v_x_2260_;
}
else
{
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
lean_inc_ref(v_es_2263_);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2280_ == 0)
{
lean_object* v_unused_2281_; 
v_unused_2281_ = lean_ctor_get(v_x_2260_, 0);
lean_dec(v_unused_2281_);
v___x_2274_ = v_x_2260_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v_x_2260_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_array_set(v_es_2263_, v_j_2267_, v___x_2264_);
lean_dec(v_j_2267_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
case 1:
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2316_; 
lean_inc_ref(v_es_2263_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_x_2260_, 0);
lean_dec(v_unused_2317_);
v___x_2283_ = v_x_2260_;
v_isShared_2284_ = v_isSharedCheck_2316_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v_x_2260_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2316_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_node_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2315_; 
v_node_2285_ = lean_ctor_get(v_entry_2268_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_entry_2268_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2287_ = v_entry_2268_;
v_isShared_2288_ = v_isSharedCheck_2315_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_node_2285_);
lean_dec(v_entry_2268_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2315_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
size_t v___x_2289_; lean_object* v_entries_2290_; size_t v___x_2291_; lean_object* v_newNode_2292_; lean_object* v___x_2293_; 
v___x_2289_ = ((size_t)5ULL);
v_entries_2290_ = lean_array_set(v_es_2263_, v_j_2267_, v___x_2264_);
v___x_2291_ = lean_usize_shift_right(v_x_2261_, v___x_2289_);
v_newNode_2292_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2285_, v___x_2291_, v_x_2262_);
lean_inc_ref(v_newNode_2292_);
v___x_2293_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2295_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_newNode_2292_);
v___x_2295_ = v___x_2287_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_newNode_2292_);
v___x_2295_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_array_set(v_entries_2290_, v_j_2267_, v___x_2295_);
lean_dec(v_j_2267_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2296_);
v___x_2298_ = v___x_2283_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_val_2301_; lean_object* v_fst_2302_; lean_object* v_snd_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_newNode_2292_);
lean_del_object(v___x_2287_);
v_val_2301_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2301_);
lean_dec_ref_known(v___x_2293_, 1);
v_fst_2302_ = lean_ctor_get(v_val_2301_, 0);
v_snd_2303_ = lean_ctor_get(v_val_2301_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_val_2301_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2305_ = v_val_2301_;
v_isShared_2306_ = v_isSharedCheck_2314_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_snd_2303_);
lean_inc(v_fst_2302_);
lean_dec(v_val_2301_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2314_;
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
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_fst_2302_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_snd_2303_);
v___x_2308_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_array_set(v_entries_2290_, v_j_2267_, v___x_2308_);
lean_dec(v_j_2267_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2309_);
v___x_2311_ = v___x_2283_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
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
}
}
}
default: 
{
lean_dec(v_j_2267_);
return v_x_2260_;
}
}
}
else
{
lean_object* v_ks_2318_; lean_object* v_vs_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2333_; 
v_ks_2318_ = lean_ctor_get(v_x_2260_, 0);
v_vs_2319_ = lean_ctor_get(v_x_2260_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_x_2260_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2321_ = v_x_2260_;
v_isShared_2322_ = v_isSharedCheck_2333_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_vs_2319_);
lean_inc(v_ks_2318_);
lean_dec(v_x_2260_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2333_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2318_, v_x_2262_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2325_; 
if (v_isShared_2322_ == 0)
{
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_ks_2318_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_vs_2319_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_object* v_val_2327_; lean_object* v_keys_x27_2328_; lean_object* v_vals_x27_2329_; lean_object* v___x_2331_; 
v_val_2327_ = lean_ctor_get(v___x_2323_, 0);
lean_inc_n(v_val_2327_, 2);
lean_dec_ref_known(v___x_2323_, 1);
v_keys_x27_2328_ = l_Array_eraseIdx___redArg(v_ks_2318_, v_val_2327_);
v_vals_x27_2329_ = l_Array_eraseIdx___redArg(v_vs_2319_, v_val_2327_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v_vals_x27_2329_);
lean_ctor_set(v___x_2321_, 0, v_keys_x27_2328_);
v___x_2331_ = v___x_2321_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_keys_x27_2328_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_vals_x27_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
size_t v_x_19465__boxed_2337_; lean_object* v_res_2338_; 
v_x_19465__boxed_2337_ = lean_unbox_usize(v_x_2335_);
lean_dec(v_x_2335_);
v_res_2338_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2334_, v_x_19465__boxed_2337_, v_x_2336_);
lean_dec_ref(v_x_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v___x_2341_; size_t v___x_2342_; size_t v___x_2343_; uint64_t v___x_2344_; size_t v_h_2345_; lean_object* v___x_2346_; 
v___x_2341_ = lean_ptr_addr(v_x_2340_);
v___x_2342_ = ((size_t)3ULL);
v___x_2343_ = lean_usize_shift_right(v___x_2341_, v___x_2342_);
v___x_2344_ = lean_usize_to_uint64(v___x_2343_);
v_h_2345_ = lean_uint64_to_usize(v___x_2344_);
v___x_2346_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2339_, v_h_2345_, v_x_2340_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2347_, v_x_2348_);
lean_dec_ref(v_x_2348_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
if (lean_obj_tag(v_as_2350_) == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
else
{
lean_object* v_head_2364_; lean_object* v_tail_2365_; lean_object* v___x_2366_; 
v_head_2364_ = lean_ctor_get(v_as_2350_, 0);
lean_inc(v_head_2364_);
v_tail_2365_ = lean_ctor_get(v_as_2350_, 1);
lean_inc(v_tail_2365_);
lean_dec_ref_known(v_as_2350_, 2);
v___x_2366_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2364_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_dec_ref_known(v___x_2366_, 1);
v_as_2350_ = v_tail_2365_;
goto _start;
}
else
{
lean_dec(v_tail_2365_);
return v___x_2366_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec(v___y_2369_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2381_, lean_object* v_vals_2382_, lean_object* v_i_2383_, lean_object* v_k_2384_){
_start:
{
lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = lean_array_get_size(v_keys_2381_);
v___x_2386_ = lean_nat_dec_lt(v_i_2383_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_dec(v_i_2383_);
v___x_2387_ = lean_box(0);
return v___x_2387_;
}
else
{
lean_object* v_k_x27_2388_; size_t v___x_2389_; size_t v___x_2390_; uint8_t v___x_2391_; 
v_k_x27_2388_ = lean_array_fget_borrowed(v_keys_2381_, v_i_2383_);
v___x_2389_ = lean_ptr_addr(v_k_2384_);
v___x_2390_ = lean_ptr_addr(v_k_x27_2388_);
v___x_2391_ = lean_usize_dec_eq(v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_add(v_i_2383_, v___x_2392_);
lean_dec(v_i_2383_);
v_i_2383_ = v___x_2393_;
goto _start;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_array_fget_borrowed(v_vals_2382_, v_i_2383_);
lean_dec(v_i_2383_);
lean_inc(v___x_2395_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2397_, lean_object* v_vals_2398_, lean_object* v_i_2399_, lean_object* v_k_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2397_, v_vals_2398_, v_i_2399_, v_k_2400_);
lean_dec_ref(v_k_2400_);
lean_dec_ref(v_vals_2398_);
lean_dec_ref(v_keys_2397_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2402_, size_t v_x_2403_, lean_object* v_x_2404_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
lean_object* v_es_2405_; lean_object* v___x_2406_; size_t v___x_2407_; size_t v___x_2408_; lean_object* v_j_2409_; lean_object* v___x_2410_; 
v_es_2405_ = lean_ctor_get(v_x_2402_, 0);
v___x_2406_ = lean_box(2);
v___x_2407_ = ((size_t)31ULL);
v___x_2408_ = lean_usize_land(v_x_2403_, v___x_2407_);
v_j_2409_ = lean_usize_to_nat(v___x_2408_);
v___x_2410_ = lean_array_get_borrowed(v___x_2406_, v_es_2405_, v_j_2409_);
lean_dec(v_j_2409_);
switch(lean_obj_tag(v___x_2410_))
{
case 0:
{
lean_object* v_key_2411_; lean_object* v_val_2412_; size_t v___x_2413_; size_t v___x_2414_; uint8_t v___x_2415_; 
v_key_2411_ = lean_ctor_get(v___x_2410_, 0);
v_val_2412_ = lean_ctor_get(v___x_2410_, 1);
v___x_2413_ = lean_ptr_addr(v_x_2404_);
v___x_2414_ = lean_ptr_addr(v_key_2411_);
v___x_2415_ = lean_usize_dec_eq(v___x_2413_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_box(0);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; 
lean_inc(v_val_2412_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_val_2412_);
return v___x_2417_;
}
}
case 1:
{
lean_object* v_node_2418_; size_t v___x_2419_; size_t v___x_2420_; 
v_node_2418_ = lean_ctor_get(v___x_2410_, 0);
v___x_2419_ = ((size_t)5ULL);
v___x_2420_ = lean_usize_shift_right(v_x_2403_, v___x_2419_);
v_x_2402_ = v_node_2418_;
v_x_2403_ = v___x_2420_;
goto _start;
}
default: 
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_box(0);
return v___x_2422_;
}
}
}
else
{
lean_object* v_ks_2423_; lean_object* v_vs_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_ks_2423_ = lean_ctor_get(v_x_2402_, 0);
v_vs_2424_ = lean_ctor_get(v_x_2402_, 1);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2423_, v_vs_2424_, v___x_2425_, v_x_2404_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
size_t v_x_19690__boxed_2430_; lean_object* v_res_2431_; 
v_x_19690__boxed_2430_ = lean_unbox_usize(v_x_2428_);
lean_dec(v_x_2428_);
v_res_2431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2427_, v_x_19690__boxed_2430_, v_x_2429_);
lean_dec_ref(v_x_2429_);
lean_dec_ref(v_x_2427_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
size_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; uint64_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2434_ = lean_ptr_addr(v_x_2433_);
v___x_2435_ = ((size_t)3ULL);
v___x_2436_ = lean_usize_shift_right(v___x_2434_, v___x_2435_);
v___x_2437_ = lean_usize_to_uint64(v___x_2436_);
v___x_2438_ = lean_uint64_to_usize(v___x_2437_);
v___x_2439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2432_, v___x_2438_, v_x_2433_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2440_, v_x_2441_);
lean_dec_ref(v_x_2441_);
lean_dec_ref(v_x_2440_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2443_, lean_object* v_b_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
if (lean_obj_tag(v_as_x27_2443_) == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_b_2444_);
return v___x_2456_;
}
else
{
lean_object* v_head_2457_; lean_object* v_tail_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_toGoalState_2461_; lean_object* v_ematch_2462_; lean_object* v_delayedThmInsts_2463_; lean_object* v___x_2464_; 
v_head_2457_ = lean_ctor_get(v_as_x27_2443_, 0);
v_tail_2458_ = lean_ctor_get(v_as_x27_2443_, 1);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_st_ref_get(v___y_2445_);
v_toGoalState_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_ref(v_toGoalState_2461_);
lean_dec(v___x_2460_);
v_ematch_2462_ = lean_ctor_get(v_toGoalState_2461_, 13);
lean_inc_ref(v_ematch_2462_);
lean_dec_ref(v_toGoalState_2461_);
v_delayedThmInsts_2463_ = lean_ctor_get(v_ematch_2462_, 10);
lean_inc_ref(v_delayedThmInsts_2463_);
lean_dec_ref(v_ematch_2462_);
v___x_2464_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2463_, v_head_2457_);
lean_dec_ref(v_delayedThmInsts_2463_);
if (lean_obj_tag(v___x_2464_) == 1)
{
lean_object* v_val_2465_; lean_object* v___x_2466_; lean_object* v_toGoalState_2467_; lean_object* v_ematch_2468_; lean_object* v_mvarId_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2524_; 
v_val_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = lean_st_ref_take(v___y_2445_);
v_toGoalState_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_toGoalState_2467_);
v_ematch_2468_ = lean_ctor_get(v_toGoalState_2467_, 13);
lean_inc_ref(v_ematch_2468_);
v_mvarId_2469_ = lean_ctor_get(v___x_2466_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2525_);
v___x_2471_ = v___x_2466_;
v_isShared_2472_ = v_isSharedCheck_2524_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_mvarId_2469_);
lean_dec(v___x_2466_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2524_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_nextDeclIdx_2473_; lean_object* v_enodeMap_2474_; lean_object* v_exprs_2475_; lean_object* v_parents_2476_; lean_object* v_congrTable_2477_; lean_object* v_appMap_2478_; lean_object* v_indicesFound_2479_; lean_object* v_toProcess_2480_; lean_object* v_internalizing_2481_; uint8_t v_inconsistent_2482_; lean_object* v_nextIdx_2483_; lean_object* v_newRawFacts_2484_; lean_object* v_facts_2485_; lean_object* v_extThms_2486_; lean_object* v_inj_2487_; lean_object* v_split_2488_; lean_object* v_clean_2489_; lean_object* v_sstates_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2522_; 
v_nextDeclIdx_2473_ = lean_ctor_get(v_toGoalState_2467_, 0);
v_enodeMap_2474_ = lean_ctor_get(v_toGoalState_2467_, 1);
v_exprs_2475_ = lean_ctor_get(v_toGoalState_2467_, 2);
v_parents_2476_ = lean_ctor_get(v_toGoalState_2467_, 3);
v_congrTable_2477_ = lean_ctor_get(v_toGoalState_2467_, 4);
v_appMap_2478_ = lean_ctor_get(v_toGoalState_2467_, 5);
v_indicesFound_2479_ = lean_ctor_get(v_toGoalState_2467_, 6);
v_toProcess_2480_ = lean_ctor_get(v_toGoalState_2467_, 7);
v_internalizing_2481_ = lean_ctor_get(v_toGoalState_2467_, 8);
v_inconsistent_2482_ = lean_ctor_get_uint8(v_toGoalState_2467_, sizeof(void*)*18);
v_nextIdx_2483_ = lean_ctor_get(v_toGoalState_2467_, 9);
v_newRawFacts_2484_ = lean_ctor_get(v_toGoalState_2467_, 10);
v_facts_2485_ = lean_ctor_get(v_toGoalState_2467_, 11);
v_extThms_2486_ = lean_ctor_get(v_toGoalState_2467_, 12);
v_inj_2487_ = lean_ctor_get(v_toGoalState_2467_, 14);
v_split_2488_ = lean_ctor_get(v_toGoalState_2467_, 15);
v_clean_2489_ = lean_ctor_get(v_toGoalState_2467_, 16);
v_sstates_2490_ = lean_ctor_get(v_toGoalState_2467_, 17);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_toGoalState_2467_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v_toGoalState_2467_, 13);
lean_dec(v_unused_2523_);
v___x_2492_ = v_toGoalState_2467_;
v_isShared_2493_ = v_isSharedCheck_2522_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_sstates_2490_);
lean_inc(v_clean_2489_);
lean_inc(v_split_2488_);
lean_inc(v_inj_2487_);
lean_inc(v_extThms_2486_);
lean_inc(v_facts_2485_);
lean_inc(v_newRawFacts_2484_);
lean_inc(v_nextIdx_2483_);
lean_inc(v_internalizing_2481_);
lean_inc(v_toProcess_2480_);
lean_inc(v_indicesFound_2479_);
lean_inc(v_appMap_2478_);
lean_inc(v_congrTable_2477_);
lean_inc(v_parents_2476_);
lean_inc(v_exprs_2475_);
lean_inc(v_enodeMap_2474_);
lean_inc(v_nextDeclIdx_2473_);
lean_dec(v_toGoalState_2467_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2522_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_thmMap_2494_; lean_object* v_gmt_2495_; lean_object* v_thms_2496_; lean_object* v_newThms_2497_; lean_object* v_numInstances_2498_; lean_object* v_numDelayedInstances_2499_; lean_object* v_num_2500_; lean_object* v_preInstances_2501_; lean_object* v_nextThmIdx_2502_; lean_object* v_matchEqNames_2503_; lean_object* v_delayedThmInsts_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2521_; 
v_thmMap_2494_ = lean_ctor_get(v_ematch_2468_, 0);
v_gmt_2495_ = lean_ctor_get(v_ematch_2468_, 1);
v_thms_2496_ = lean_ctor_get(v_ematch_2468_, 2);
v_newThms_2497_ = lean_ctor_get(v_ematch_2468_, 3);
v_numInstances_2498_ = lean_ctor_get(v_ematch_2468_, 4);
v_numDelayedInstances_2499_ = lean_ctor_get(v_ematch_2468_, 5);
v_num_2500_ = lean_ctor_get(v_ematch_2468_, 6);
v_preInstances_2501_ = lean_ctor_get(v_ematch_2468_, 7);
v_nextThmIdx_2502_ = lean_ctor_get(v_ematch_2468_, 8);
v_matchEqNames_2503_ = lean_ctor_get(v_ematch_2468_, 9);
v_delayedThmInsts_2504_ = lean_ctor_get(v_ematch_2468_, 10);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_ematch_2468_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2506_ = v_ematch_2468_;
v_isShared_2507_ = v_isSharedCheck_2521_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_delayedThmInsts_2504_);
lean_inc(v_matchEqNames_2503_);
lean_inc(v_nextThmIdx_2502_);
lean_inc(v_preInstances_2501_);
lean_inc(v_num_2500_);
lean_inc(v_numDelayedInstances_2499_);
lean_inc(v_numInstances_2498_);
lean_inc(v_newThms_2497_);
lean_inc(v_thms_2496_);
lean_inc(v_gmt_2495_);
lean_inc(v_thmMap_2494_);
lean_dec(v_ematch_2468_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2521_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2504_, v_head_2457_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 10, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_thmMap_2494_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_gmt_2495_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_thms_2496_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_newThms_2497_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_numInstances_2498_);
lean_ctor_set(v_reuseFailAlloc_2520_, 5, v_numDelayedInstances_2499_);
lean_ctor_set(v_reuseFailAlloc_2520_, 6, v_num_2500_);
lean_ctor_set(v_reuseFailAlloc_2520_, 7, v_preInstances_2501_);
lean_ctor_set(v_reuseFailAlloc_2520_, 8, v_nextThmIdx_2502_);
lean_ctor_set(v_reuseFailAlloc_2520_, 9, v_matchEqNames_2503_);
lean_ctor_set(v_reuseFailAlloc_2520_, 10, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 13, v___x_2510_);
v___x_2512_ = v___x_2492_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_nextDeclIdx_2473_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_enodeMap_2474_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_exprs_2475_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_parents_2476_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_congrTable_2477_);
lean_ctor_set(v_reuseFailAlloc_2519_, 5, v_appMap_2478_);
lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_indicesFound_2479_);
lean_ctor_set(v_reuseFailAlloc_2519_, 7, v_toProcess_2480_);
lean_ctor_set(v_reuseFailAlloc_2519_, 8, v_internalizing_2481_);
lean_ctor_set(v_reuseFailAlloc_2519_, 9, v_nextIdx_2483_);
lean_ctor_set(v_reuseFailAlloc_2519_, 10, v_newRawFacts_2484_);
lean_ctor_set(v_reuseFailAlloc_2519_, 11, v_facts_2485_);
lean_ctor_set(v_reuseFailAlloc_2519_, 12, v_extThms_2486_);
lean_ctor_set(v_reuseFailAlloc_2519_, 13, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2519_, 14, v_inj_2487_);
lean_ctor_set(v_reuseFailAlloc_2519_, 15, v_split_2488_);
lean_ctor_set(v_reuseFailAlloc_2519_, 16, v_clean_2489_);
lean_ctor_set(v_reuseFailAlloc_2519_, 17, v_sstates_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*18, v_inconsistent_2482_);
v___x_2512_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2512_);
v___x_2514_ = v___x_2471_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_mvarId_2469_);
v___x_2514_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_st_ref_put(v___y_2445_, v___x_2514_);
v___x_2516_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2465_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_dec_ref_known(v___x_2516_, 1);
v_as_x27_2443_ = v_tail_2458_;
v_b_2444_ = v___x_2459_;
goto _start;
}
else
{
return v___x_2516_;
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
lean_dec(v___x_2464_);
v_as_x27_2443_ = v_tail_2458_;
v_b_2444_ = v___x_2459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2527_, lean_object* v_b_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2527_, v_b_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec(v_as_x27_2527_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2542_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2582_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2582_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2582_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_unbox(v_a_2554_);
lean_dec(v_a_2554_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v_toGoalState_2560_; lean_object* v_ematch_2561_; lean_object* v_delayedThmInsts_2562_; uint8_t v___x_2563_; 
v___x_2559_ = lean_st_ref_get(v_a_2542_);
v_toGoalState_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref(v_toGoalState_2560_);
lean_dec(v___x_2559_);
v_ematch_2561_ = lean_ctor_get(v_toGoalState_2560_, 13);
lean_inc_ref(v_ematch_2561_);
lean_dec_ref(v_toGoalState_2560_);
v_delayedThmInsts_2562_ = lean_ctor_get(v_ematch_2561_, 10);
lean_inc_ref(v_delayedThmInsts_2562_);
lean_dec_ref(v_ematch_2561_);
v___x_2563_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2562_);
lean_dec_ref(v_delayedThmInsts_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_del_object(v___x_2556_);
v___x_2564_ = lean_box(0);
v___x_2565_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2541_, v___x_2564_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2573_);
v___x_2567_ = v___x_2565_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2565_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2564_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2564_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
return v___x_2565_;
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(0);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2574_);
v___x_2576_ = v___x_2556_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
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
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_box(0);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2578_);
v___x_2580_ = v___x_2556_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2553_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2553_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec(v_toPropagateDown_2591_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2605_, v_x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2608_, v_x_2609_, v_x_2610_);
lean_dec_ref(v_x_2610_);
lean_dec_ref(v_x_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2613_, v_x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2616_, v_x_2617_, v_x_2618_);
lean_dec_ref(v_x_2618_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2620_, lean_object* v_as_x27_2621_, lean_object* v_b_2622_, lean_object* v_a_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2621_, v_b_2622_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v_a_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2636_, v_as_x27_2637_, v_b_2638_, v_a_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v_as_x27_2637_);
lean_dec(v_as_2636_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2652_, lean_object* v_x_2653_, size_t v_x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2653_, v_x_2654_, v_x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
size_t v_x_19995__boxed_2661_; lean_object* v_res_2662_; 
v_x_19995__boxed_2661_ = lean_unbox_usize(v_x_2659_);
lean_dec(v_x_2659_);
v_res_2662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2657_, v_x_2658_, v_x_19995__boxed_2661_, v_x_2660_);
lean_dec_ref(v_x_2660_);
lean_dec_ref(v_x_2658_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2663_, lean_object* v_x_2664_, size_t v_x_2665_, lean_object* v_x_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2664_, v_x_2665_, v_x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2668_, lean_object* v_x_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_){
_start:
{
size_t v_x_20006__boxed_2672_; lean_object* v_res_2673_; 
v_x_20006__boxed_2672_ = lean_unbox_usize(v_x_2670_);
lean_dec(v_x_2670_);
v_res_2673_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2668_, v_x_2669_, v_x_20006__boxed_2672_, v_x_2671_);
lean_dec_ref(v_x_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2674_, lean_object* v_keys_2675_, lean_object* v_vals_2676_, lean_object* v_heq_2677_, lean_object* v_i_2678_, lean_object* v_k_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2675_, v_vals_2676_, v_i_2678_, v_k_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2681_, lean_object* v_keys_2682_, lean_object* v_vals_2683_, lean_object* v_heq_2684_, lean_object* v_i_2685_, lean_object* v_k_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2681_, v_keys_2682_, v_vals_2683_, v_heq_2684_, v_i_2685_, v_k_2686_);
lean_dec_ref(v_k_2686_);
lean_dec_ref(v_vals_2683_);
lean_dec_ref(v_keys_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2688_, lean_object* v_keys_2689_, lean_object* v_vals_2690_, lean_object* v_i_2691_, lean_object* v_k_2692_){
_start:
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = lean_array_get_size(v_keys_2689_);
v___x_2694_ = lean_nat_dec_lt(v_i_2691_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; 
lean_dec_ref(v_k_2692_);
lean_dec(v_i_2691_);
v___x_2695_ = lean_box(0);
return v___x_2695_;
}
else
{
lean_object* v_k_x27_2696_; uint8_t v___x_2697_; 
v_k_x27_2696_ = lean_array_fget_borrowed(v_keys_2689_, v_i_2691_);
lean_inc(v_k_x27_2696_);
lean_inc_ref(v_k_2692_);
v___x_2697_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2688_, v_k_2692_, v_k_x27_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_nat_add(v_i_2691_, v___x_2698_);
lean_dec(v_i_2691_);
v_i_2691_ = v___x_2699_;
goto _start;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec_ref(v_k_2692_);
v___x_2701_ = lean_array_fget_borrowed(v_vals_2690_, v_i_2691_);
lean_dec(v_i_2691_);
lean_inc(v___x_2701_);
lean_inc(v_k_x27_2696_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_k_x27_2696_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2704_, lean_object* v_keys_2705_, lean_object* v_vals_2706_, lean_object* v_i_2707_, lean_object* v_k_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2704_, v_keys_2705_, v_vals_2706_, v_i_2707_, v_k_2708_);
lean_dec_ref(v_vals_2706_);
lean_dec_ref(v_keys_2705_);
lean_dec_ref(v___x_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2710_, lean_object* v_x_2711_, size_t v_x_2712_, lean_object* v_x_2713_){
_start:
{
if (lean_obj_tag(v_x_2711_) == 0)
{
lean_object* v_es_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v_j_2718_; lean_object* v___x_2719_; 
v_es_2714_ = lean_ctor_get(v_x_2711_, 0);
lean_inc_ref(v_es_2714_);
lean_dec_ref_known(v_x_2711_, 1);
v___x_2715_ = lean_box(2);
v___x_2716_ = ((size_t)31ULL);
v___x_2717_ = lean_usize_land(v_x_2712_, v___x_2716_);
v_j_2718_ = lean_usize_to_nat(v___x_2717_);
v___x_2719_ = lean_array_get(v___x_2715_, v_es_2714_, v_j_2718_);
lean_dec(v_j_2718_);
lean_dec_ref(v_es_2714_);
switch(lean_obj_tag(v___x_2719_))
{
case 0:
{
lean_object* v_key_2720_; lean_object* v_val_2721_; uint8_t v___x_2722_; 
v_key_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc_n(v_key_2720_, 2);
v_val_2721_ = lean_ctor_get(v___x_2719_, 1);
lean_inc(v_val_2721_);
lean_dec_ref_known(v___x_2719_, 2);
v___x_2722_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2710_, v_x_2713_, v_key_2720_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_dec(v_val_2721_);
lean_dec(v_key_2720_);
v___x_2723_ = lean_box(0);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_key_2720_);
lean_ctor_set(v___x_2724_, 1, v_val_2721_);
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
}
case 1:
{
lean_object* v_node_2726_; size_t v___x_2727_; size_t v___x_2728_; 
v_node_2726_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_node_2726_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2727_ = ((size_t)5ULL);
v___x_2728_ = lean_usize_shift_right(v_x_2712_, v___x_2727_);
v_x_2711_ = v_node_2726_;
v_x_2712_ = v___x_2728_;
goto _start;
}
default: 
{
lean_object* v___x_2730_; 
lean_dec_ref(v_x_2713_);
v___x_2730_ = lean_box(0);
return v___x_2730_;
}
}
}
else
{
lean_object* v_ks_2731_; lean_object* v_vs_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_ks_2731_ = lean_ctor_get(v_x_2711_, 0);
lean_inc_ref(v_ks_2731_);
v_vs_2732_ = lean_ctor_get(v_x_2711_, 1);
lean_inc_ref(v_vs_2732_);
lean_dec_ref_known(v_x_2711_, 2);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2710_, v_ks_2731_, v_vs_2732_, v___x_2733_, v_x_2713_);
lean_dec_ref(v_vs_2732_);
lean_dec_ref(v_ks_2731_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
size_t v_x_26131__boxed_2739_; lean_object* v_res_2740_; 
v_x_26131__boxed_2739_ = lean_unbox_usize(v_x_2737_);
lean_dec(v_x_2737_);
v_res_2740_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2735_, v_x_2736_, v_x_26131__boxed_2739_, v_x_2738_);
lean_dec_ref(v___x_2735_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_){
_start:
{
uint64_t v___x_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
lean_inc_ref(v_x_2743_);
v___x_2744_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2741_, v_x_2743_);
v___x_2745_ = lean_uint64_to_usize(v___x_2744_);
lean_inc_ref(v_x_2742_);
v___x_2746_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2741_, v_x_2742_, v___x_2745_, v_x_2743_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2747_, v_x_2748_, v_x_2749_);
lean_dec_ref(v_x_2748_);
lean_dec_ref(v___x_2747_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v_ks_2756_; lean_object* v_vs_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2781_; 
v_ks_2756_ = lean_ctor_get(v_x_2752_, 0);
v_vs_2757_ = lean_ctor_get(v_x_2752_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_x_2752_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2759_ = v_x_2752_;
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_vs_2757_);
lean_inc(v_ks_2756_);
lean_dec(v_x_2752_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = lean_array_get_size(v_ks_2756_);
v___x_2762_ = lean_nat_dec_lt(v_x_2753_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
lean_dec(v_x_2753_);
v___x_2763_ = lean_array_push(v_ks_2756_, v_x_2754_);
v___x_2764_ = lean_array_push(v_vs_2757_, v_x_2755_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___x_2764_);
lean_ctor_set(v___x_2759_, 0, v___x_2763_);
v___x_2766_ = v___x_2759_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
else
{
lean_object* v_k_x27_2768_; uint8_t v___x_2769_; 
v_k_x27_2768_ = lean_array_fget_borrowed(v_ks_2756_, v_x_2753_);
lean_inc(v_k_x27_2768_);
lean_inc_ref(v_x_2754_);
v___x_2769_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2751_, v_x_2754_, v_k_x27_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2771_; 
if (v_isShared_2760_ == 0)
{
v___x_2771_ = v___x_2759_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_ks_2756_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_vs_2757_);
v___x_2771_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_unsigned_to_nat(1u);
v___x_2773_ = lean_nat_add(v_x_2753_, v___x_2772_);
lean_dec(v_x_2753_);
v_x_2752_ = v___x_2771_;
v_x_2753_ = v___x_2773_;
goto _start;
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2776_ = lean_array_fset(v_ks_2756_, v_x_2753_, v_x_2754_);
v___x_2777_ = lean_array_fset(v_vs_2757_, v_x_2753_, v_x_2755_);
lean_dec(v_x_2753_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 1, v___x_2777_);
lean_ctor_set(v___x_2759_, 0, v___x_2776_);
v___x_2779_ = v___x_2759_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2782_, v_x_2783_, v_x_2784_, v_x_2785_, v_x_2786_);
lean_dec_ref(v___x_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2788_, lean_object* v_n_2789_, lean_object* v_k_2790_, lean_object* v_v_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2788_, v_n_2789_, v___x_2792_, v_k_2790_, v_v_2791_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2794_, lean_object* v_n_2795_, lean_object* v_k_2796_, lean_object* v_v_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2794_, v_n_2795_, v_k_2796_, v_v_2797_);
lean_dec_ref(v___x_2794_);
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2800_, lean_object* v_x_2801_, size_t v_x_2802_, size_t v_x_2803_, lean_object* v_x_2804_, lean_object* v_x_2805_){
_start:
{
if (lean_obj_tag(v_x_2801_) == 0)
{
lean_object* v_es_2806_; size_t v___x_2807_; size_t v___x_2808_; lean_object* v_j_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_es_2806_ = lean_ctor_get(v_x_2801_, 0);
v___x_2807_ = ((size_t)31ULL);
v___x_2808_ = lean_usize_land(v_x_2802_, v___x_2807_);
v_j_2809_ = lean_usize_to_nat(v___x_2808_);
v___x_2810_ = lean_array_get_size(v_es_2806_);
v___x_2811_ = lean_nat_dec_lt(v_j_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_dec(v_j_2809_);
lean_dec(v_x_2805_);
lean_dec_ref(v_x_2804_);
return v_x_2801_;
}
else
{
lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2850_; 
lean_inc_ref(v_es_2806_);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2801_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; 
v_unused_2851_ = lean_ctor_get(v_x_2801_, 0);
lean_dec(v_unused_2851_);
v___x_2813_ = v_x_2801_;
v_isShared_2814_ = v_isSharedCheck_2850_;
goto v_resetjp_2812_;
}
else
{
lean_dec(v_x_2801_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2850_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_v_2815_; lean_object* v___x_2816_; lean_object* v_xs_x27_2817_; lean_object* v___y_2819_; 
v_v_2815_ = lean_array_fget(v_es_2806_, v_j_2809_);
v___x_2816_ = lean_box(0);
v_xs_x27_2817_ = lean_array_fset(v_es_2806_, v_j_2809_, v___x_2816_);
switch(lean_obj_tag(v_v_2815_))
{
case 0:
{
lean_object* v_key_2824_; lean_object* v_val_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2835_; 
v_key_2824_ = lean_ctor_get(v_v_2815_, 0);
v_val_2825_ = lean_ctor_get(v_v_2815_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_v_2815_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2827_ = v_v_2815_;
v_isShared_2828_ = v_isSharedCheck_2835_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_val_2825_);
lean_inc(v_key_2824_);
lean_dec(v_v_2815_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2835_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
uint8_t v___x_2829_; 
lean_inc(v_key_2824_);
lean_inc_ref(v_x_2804_);
v___x_2829_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2800_, v_x_2804_, v_key_2824_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2827_);
v___x_2830_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2824_, v_val_2825_, v_x_2804_, v_x_2805_);
v___x_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
v___y_2819_ = v___x_2831_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2833_; 
lean_dec(v_val_2825_);
lean_dec(v_key_2824_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 1, v_x_2805_);
lean_ctor_set(v___x_2827_, 0, v_x_2804_);
v___x_2833_ = v___x_2827_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_x_2804_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_x_2805_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
v___y_2819_ = v___x_2833_;
goto v___jp_2818_;
}
}
}
}
case 1:
{
lean_object* v_node_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2848_; 
v_node_2836_ = lean_ctor_get(v_v_2815_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_v_2815_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2838_ = v_v_2815_;
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_node_2836_);
lean_dec(v_v_2815_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
size_t v___x_2840_; size_t v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2840_ = ((size_t)5ULL);
v___x_2841_ = lean_usize_shift_right(v_x_2802_, v___x_2840_);
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_add(v_x_2803_, v___x_2842_);
v___x_2844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2800_, v_node_2836_, v___x_2841_, v___x_2843_, v_x_2804_, v_x_2805_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2844_);
v___x_2846_ = v___x_2838_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v___y_2819_ = v___x_2846_;
goto v___jp_2818_;
}
}
}
default: 
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_x_2804_);
lean_ctor_set(v___x_2849_, 1, v_x_2805_);
v___y_2819_ = v___x_2849_;
goto v___jp_2818_;
}
}
v___jp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = lean_array_fset(v_xs_x27_2817_, v_j_2809_, v___y_2819_);
lean_dec(v_j_2809_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2820_);
v___x_2822_ = v___x_2813_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
else
{
lean_object* v_ks_2852_; lean_object* v_vs_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2871_; 
v_ks_2852_ = lean_ctor_get(v_x_2801_, 0);
v_vs_2853_ = lean_ctor_get(v_x_2801_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2801_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2855_ = v_x_2801_;
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_vs_2853_);
lean_inc(v_ks_2852_);
lean_dec(v_x_2801_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2871_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_ks_2852_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_vs_2853_);
v___x_2858_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v_newNode_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v_newNode_2859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2800_, v___x_2858_, v_x_2804_, v_x_2805_);
v___x_2860_ = ((size_t)7ULL);
v___x_2861_ = lean_usize_dec_le(v___x_2860_, v_x_2803_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2862_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2859_);
v___x_2863_ = lean_unsigned_to_nat(4u);
v___x_2864_ = lean_nat_dec_lt(v___x_2862_, v___x_2863_);
lean_dec(v___x_2862_);
if (v___x_2864_ == 0)
{
lean_object* v_ks_2865_; lean_object* v_vs_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_ks_2865_ = lean_ctor_get(v_newNode_2859_, 0);
lean_inc_ref(v_ks_2865_);
v_vs_2866_ = lean_ctor_get(v_newNode_2859_, 1);
lean_inc_ref(v_vs_2866_);
lean_dec_ref(v_newNode_2859_);
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2800_, v_x_2803_, v_ks_2865_, v_vs_2866_, v___x_2867_, v___x_2868_);
lean_dec_ref(v_vs_2866_);
lean_dec_ref(v_ks_2865_);
return v___x_2869_;
}
else
{
return v_newNode_2859_;
}
}
else
{
return v_newNode_2859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2872_, size_t v_depth_2873_, lean_object* v_keys_2874_, lean_object* v_vals_2875_, lean_object* v_i_2876_, lean_object* v_entries_2877_){
_start:
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = lean_array_get_size(v_keys_2874_);
v___x_2879_ = lean_nat_dec_lt(v_i_2876_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_dec(v_i_2876_);
return v_entries_2877_;
}
else
{
lean_object* v_k_2880_; lean_object* v_v_2881_; uint64_t v___x_2882_; size_t v_h_2883_; size_t v___x_2884_; lean_object* v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; size_t v_h_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_k_2880_ = lean_array_fget_borrowed(v_keys_2874_, v_i_2876_);
v_v_2881_ = lean_array_fget_borrowed(v_vals_2875_, v_i_2876_);
lean_inc_n(v_k_2880_, 2);
v___x_2882_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2872_, v_k_2880_);
v_h_2883_ = lean_uint64_to_usize(v___x_2882_);
v___x_2884_ = ((size_t)5ULL);
v___x_2885_ = lean_unsigned_to_nat(1u);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_sub(v_depth_2873_, v___x_2886_);
v___x_2888_ = lean_usize_mul(v___x_2884_, v___x_2887_);
v_h_2889_ = lean_usize_shift_right(v_h_2883_, v___x_2888_);
v___x_2890_ = lean_nat_add(v_i_2876_, v___x_2885_);
lean_dec(v_i_2876_);
lean_inc(v_v_2881_);
v___x_2891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2872_, v_entries_2877_, v_h_2889_, v_depth_2873_, v_k_2880_, v_v_2881_);
v_i_2876_ = v___x_2890_;
v_entries_2877_ = v___x_2891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2893_, lean_object* v_depth_2894_, lean_object* v_keys_2895_, lean_object* v_vals_2896_, lean_object* v_i_2897_, lean_object* v_entries_2898_){
_start:
{
size_t v_depth_boxed_2899_; lean_object* v_res_2900_; 
v_depth_boxed_2899_ = lean_unbox_usize(v_depth_2894_);
lean_dec(v_depth_2894_);
v_res_2900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2893_, v_depth_boxed_2899_, v_keys_2895_, v_vals_2896_, v_i_2897_, v_entries_2898_);
lean_dec_ref(v_vals_2896_);
lean_dec_ref(v_keys_2895_);
lean_dec_ref(v___x_2893_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2901_, lean_object* v_x_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
size_t v_x_26285__boxed_2907_; size_t v_x_26286__boxed_2908_; lean_object* v_res_2909_; 
v_x_26285__boxed_2907_ = lean_unbox_usize(v_x_2903_);
lean_dec(v_x_2903_);
v_x_26286__boxed_2908_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_res_2909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2901_, v_x_2902_, v_x_26285__boxed_2907_, v_x_26286__boxed_2908_, v_x_2905_, v_x_2906_);
lean_dec_ref(v___x_2901_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_){
_start:
{
uint64_t v___x_2914_; size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
lean_inc_ref(v_x_2912_);
v___x_2914_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2910_, v_x_2912_);
v___x_2915_ = lean_uint64_to_usize(v___x_2914_);
v___x_2916_ = ((size_t)1ULL);
v___x_2917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2910_, v_x_2911_, v___x_2915_, v___x_2916_, v_x_2912_, v_x_2913_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2918_, v_x_2919_, v_x_2920_, v_x_2921_);
lean_dec_ref(v___x_2918_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2927_, lean_object* v_rootNew_2928_, uint8_t v_a_2929_, lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_snd_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3123_; 
v_snd_2938_ = lean_ctor_get(v_a_2930_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v_a_2930_, 0);
lean_dec(v_unused_3124_);
v___x_2940_ = v_a_2930_;
v_isShared_2941_ = v_isSharedCheck_3123_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_snd_2938_);
lean_dec(v_a_2930_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3123_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = lean_box(0);
v___x_2943_ = lean_st_ref_get(v___y_2931_);
lean_inc(v_snd_2938_);
v___x_2944_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2943_, v_snd_2938_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3114_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3114_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3114_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_self_2949_; lean_object* v_next_2950_; lean_object* v_congr_2951_; lean_object* v_target_x3f_2952_; lean_object* v_proof_x3f_2953_; uint8_t v_flipped_2954_; lean_object* v_size_2955_; uint8_t v_interpreted_2956_; uint8_t v_ctor_2957_; uint8_t v_hasLambdas_2958_; uint8_t v_heqProofs_2959_; lean_object* v_idx_2960_; lean_object* v_generation_2961_; lean_object* v_mt_2962_; lean_object* v_sTerms_2963_; uint8_t v_funCC_2964_; lean_object* v_ematchDiagSource_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3112_; 
v_self_2949_ = lean_ctor_get(v_a_2945_, 0);
v_next_2950_ = lean_ctor_get(v_a_2945_, 1);
v_congr_2951_ = lean_ctor_get(v_a_2945_, 3);
v_target_x3f_2952_ = lean_ctor_get(v_a_2945_, 4);
v_proof_x3f_2953_ = lean_ctor_get(v_a_2945_, 5);
v_flipped_2954_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12);
v_size_2955_ = lean_ctor_get(v_a_2945_, 6);
v_interpreted_2956_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12 + 1);
v_ctor_2957_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12 + 2);
v_hasLambdas_2958_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12 + 3);
v_heqProofs_2959_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12 + 4);
v_idx_2960_ = lean_ctor_get(v_a_2945_, 7);
v_generation_2961_ = lean_ctor_get(v_a_2945_, 8);
v_mt_2962_ = lean_ctor_get(v_a_2945_, 9);
v_sTerms_2963_ = lean_ctor_get(v_a_2945_, 10);
v_funCC_2964_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2965_ = lean_ctor_get(v_a_2945_, 11);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v_a_2945_, 2);
lean_dec(v_unused_3113_);
v___x_2967_ = v_a_2945_;
v_isShared_2968_ = v_isSharedCheck_3112_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_ematchDiagSource_2965_);
lean_inc(v_sTerms_2963_);
lean_inc(v_mt_2962_);
lean_inc(v_generation_2961_);
lean_inc(v_idx_2960_);
lean_inc(v_size_2955_);
lean_inc(v_proof_x3f_2953_);
lean_inc(v_target_x3f_2952_);
lean_inc(v_congr_2951_);
lean_inc(v_next_2950_);
lean_inc(v_self_2949_);
lean_dec(v_a_2945_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3112_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2985_; 
lean_inc(v_ematchDiagSource_2965_);
lean_inc(v_sTerms_2963_);
lean_inc(v_mt_2962_);
lean_inc(v_generation_2961_);
lean_inc(v_idx_2960_);
lean_inc(v_size_2955_);
lean_inc(v_proof_x3f_2953_);
lean_inc(v_target_x3f_2952_);
lean_inc_ref(v_rootNew_2928_);
lean_inc_ref(v_next_2950_);
lean_inc_ref(v_self_2949_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v_rootNew_2928_);
v___x_2985_ = v___x_2967_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_self_2949_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_next_2950_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_rootNew_2928_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_congr_2951_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v_target_x3f_2952_);
lean_ctor_set(v_reuseFailAlloc_3111_, 5, v_proof_x3f_2953_);
lean_ctor_set(v_reuseFailAlloc_3111_, 6, v_size_2955_);
lean_ctor_set(v_reuseFailAlloc_3111_, 7, v_idx_2960_);
lean_ctor_set(v_reuseFailAlloc_3111_, 8, v_generation_2961_);
lean_ctor_set(v_reuseFailAlloc_3111_, 9, v_mt_2962_);
lean_ctor_set(v_reuseFailAlloc_3111_, 10, v_sTerms_2963_);
lean_ctor_set(v_reuseFailAlloc_3111_, 11, v_ematchDiagSource_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12, v_flipped_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12 + 1, v_interpreted_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12 + 2, v_ctor_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12 + 3, v_hasLambdas_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12 + 4, v_heqProofs_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3111_, sizeof(void*)*12 + 5, v_funCC_2964_);
v___x_2985_ = v_reuseFailAlloc_3111_;
goto v_reusejp_2984_;
}
v___jp_2969_:
{
size_t v___x_2970_; size_t v___x_2971_; uint8_t v___x_2972_; 
v___x_2970_ = lean_ptr_addr(v_next_2950_);
v___x_2971_ = lean_ptr_addr(v_lhs_2927_);
v___x_2972_ = lean_usize_dec_eq(v___x_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2974_; 
lean_del_object(v___x_2947_);
lean_dec(v_snd_2938_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v_next_2950_);
lean_ctor_set(v___x_2940_, 0, v___x_2942_);
v___x_2974_ = v___x_2940_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_next_2950_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
v_a_2930_ = v___x_2974_;
goto _start;
}
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_rootNew_2928_);
v___x_2977_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2977_);
v___x_2979_ = v___x_2940_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_snd_2938_);
v___x_2979_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2979_);
v___x_2981_ = v___x_2947_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; 
lean_inc_ref(v___x_2985_);
lean_inc_ref(v_self_2949_);
v___x_2986_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2949_, v___x_2985_, v___y_2931_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_dec_ref_known(v___x_2986_, 1);
if (v_a_2929_ == 0)
{
lean_dec_ref(v___x_2985_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2969_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2987_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2988_ = lean_unsigned_to_nat(3u);
v___x_2989_ = l_Lean_Expr_isAppOfArity(v_self_2949_, v___x_2987_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_dec_ref(v___x_2985_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2969_;
}
else
{
uint8_t v___x_2990_; 
v___x_2990_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2985_);
lean_dec_ref(v___x_2985_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v_toGoalState_2992_; lean_object* v_enodeMap_2993_; lean_object* v_congrTable_2994_; lean_object* v___x_2995_; 
v___x_2991_ = lean_st_ref_get(v___y_2931_);
v_toGoalState_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc_ref(v_toGoalState_2992_);
lean_dec(v___x_2991_);
v_enodeMap_2993_ = lean_ctor_get(v_toGoalState_2992_, 1);
lean_inc_ref(v_enodeMap_2993_);
v_congrTable_2994_ = lean_ctor_get(v_toGoalState_2992_, 4);
lean_inc_ref(v_congrTable_2994_);
lean_dec_ref(v_toGoalState_2992_);
lean_inc_ref(v_self_2949_);
v___x_2995_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2993_, v_congrTable_2994_, v_self_2949_);
lean_dec_ref(v_congrTable_2994_);
lean_dec_ref(v_enodeMap_2993_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2969_;
}
else
{
lean_object* v_val_2996_; lean_object* v_fst_2997_; lean_object* v___x_2998_; 
v_val_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_fst_2997_ = lean_ctor_get(v_val_2996_, 0);
lean_inc(v_fst_2997_);
lean_dec(v_val_2996_);
v___x_2998_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2997_, v___y_2932_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; uint8_t v___x_3000_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = lean_unbox(v_a_2999_);
lean_dec(v_a_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v_toGoalState_3002_; lean_object* v_mvarId_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3094_; 
v___x_3001_ = lean_st_ref_take(v___y_2931_);
v_toGoalState_3002_ = lean_ctor_get(v___x_3001_, 0);
v_mvarId_3003_ = lean_ctor_get(v___x_3001_, 1);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3005_ = v___x_3001_;
v_isShared_3006_ = v_isSharedCheck_3094_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_mvarId_3003_);
lean_inc(v_toGoalState_3002_);
lean_dec(v___x_3001_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3094_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_nextDeclIdx_3007_; lean_object* v_enodeMap_3008_; lean_object* v_exprs_3009_; lean_object* v_parents_3010_; lean_object* v_congrTable_3011_; lean_object* v_appMap_3012_; lean_object* v_indicesFound_3013_; lean_object* v_toProcess_3014_; lean_object* v_internalizing_3015_; uint8_t v_inconsistent_3016_; lean_object* v_nextIdx_3017_; lean_object* v_newRawFacts_3018_; lean_object* v_facts_3019_; lean_object* v_extThms_3020_; lean_object* v_ematch_3021_; lean_object* v_inj_3022_; lean_object* v_split_3023_; lean_object* v_clean_3024_; lean_object* v_sstates_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3093_; 
v_nextDeclIdx_3007_ = lean_ctor_get(v_toGoalState_3002_, 0);
v_enodeMap_3008_ = lean_ctor_get(v_toGoalState_3002_, 1);
v_exprs_3009_ = lean_ctor_get(v_toGoalState_3002_, 2);
v_parents_3010_ = lean_ctor_get(v_toGoalState_3002_, 3);
v_congrTable_3011_ = lean_ctor_get(v_toGoalState_3002_, 4);
v_appMap_3012_ = lean_ctor_get(v_toGoalState_3002_, 5);
v_indicesFound_3013_ = lean_ctor_get(v_toGoalState_3002_, 6);
v_toProcess_3014_ = lean_ctor_get(v_toGoalState_3002_, 7);
v_internalizing_3015_ = lean_ctor_get(v_toGoalState_3002_, 8);
v_inconsistent_3016_ = lean_ctor_get_uint8(v_toGoalState_3002_, sizeof(void*)*18);
v_nextIdx_3017_ = lean_ctor_get(v_toGoalState_3002_, 9);
v_newRawFacts_3018_ = lean_ctor_get(v_toGoalState_3002_, 10);
v_facts_3019_ = lean_ctor_get(v_toGoalState_3002_, 11);
v_extThms_3020_ = lean_ctor_get(v_toGoalState_3002_, 12);
v_ematch_3021_ = lean_ctor_get(v_toGoalState_3002_, 13);
v_inj_3022_ = lean_ctor_get(v_toGoalState_3002_, 14);
v_split_3023_ = lean_ctor_get(v_toGoalState_3002_, 15);
v_clean_3024_ = lean_ctor_get(v_toGoalState_3002_, 16);
v_sstates_3025_ = lean_ctor_get(v_toGoalState_3002_, 17);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_toGoalState_3002_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3027_ = v_toGoalState_3002_;
v_isShared_3028_ = v_isSharedCheck_3093_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_sstates_3025_);
lean_inc(v_clean_3024_);
lean_inc(v_split_3023_);
lean_inc(v_inj_3022_);
lean_inc(v_ematch_3021_);
lean_inc(v_extThms_3020_);
lean_inc(v_facts_3019_);
lean_inc(v_newRawFacts_3018_);
lean_inc(v_nextIdx_3017_);
lean_inc(v_internalizing_3015_);
lean_inc(v_toProcess_3014_);
lean_inc(v_indicesFound_3013_);
lean_inc(v_appMap_3012_);
lean_inc(v_congrTable_3011_);
lean_inc(v_parents_3010_);
lean_inc(v_exprs_3009_);
lean_inc(v_enodeMap_3008_);
lean_inc(v_nextDeclIdx_3007_);
lean_dec(v_toGoalState_3002_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3093_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3029_ = lean_box(0);
lean_inc_ref(v_self_2949_);
v___x_3030_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3008_, v_congrTable_3011_, v_self_2949_, v___x_3029_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 4, v___x_3030_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_nextDeclIdx_3007_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_enodeMap_3008_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_exprs_3009_);
lean_ctor_set(v_reuseFailAlloc_3092_, 3, v_parents_3010_);
lean_ctor_set(v_reuseFailAlloc_3092_, 4, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3092_, 5, v_appMap_3012_);
lean_ctor_set(v_reuseFailAlloc_3092_, 6, v_indicesFound_3013_);
lean_ctor_set(v_reuseFailAlloc_3092_, 7, v_toProcess_3014_);
lean_ctor_set(v_reuseFailAlloc_3092_, 8, v_internalizing_3015_);
lean_ctor_set(v_reuseFailAlloc_3092_, 9, v_nextIdx_3017_);
lean_ctor_set(v_reuseFailAlloc_3092_, 10, v_newRawFacts_3018_);
lean_ctor_set(v_reuseFailAlloc_3092_, 11, v_facts_3019_);
lean_ctor_set(v_reuseFailAlloc_3092_, 12, v_extThms_3020_);
lean_ctor_set(v_reuseFailAlloc_3092_, 13, v_ematch_3021_);
lean_ctor_set(v_reuseFailAlloc_3092_, 14, v_inj_3022_);
lean_ctor_set(v_reuseFailAlloc_3092_, 15, v_split_3023_);
lean_ctor_set(v_reuseFailAlloc_3092_, 16, v_clean_3024_);
lean_ctor_set(v_reuseFailAlloc_3092_, 17, v_sstates_3025_);
lean_ctor_set_uint8(v_reuseFailAlloc_3092_, sizeof(void*)*18, v_inconsistent_3016_);
v___x_3032_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3032_);
v___x_3034_ = v___x_3005_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_mvarId_3003_);
v___x_3034_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_st_ref_put(v___y_2931_, v___x_3034_);
lean_inc_ref(v_rootNew_2928_);
lean_inc_ref(v_next_2950_);
lean_inc_ref_n(v_self_2949_, 3);
v___x_3036_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3036_, 0, v_self_2949_);
lean_ctor_set(v___x_3036_, 1, v_next_2950_);
lean_ctor_set(v___x_3036_, 2, v_rootNew_2928_);
lean_ctor_set(v___x_3036_, 3, v_self_2949_);
lean_ctor_set(v___x_3036_, 4, v_target_x3f_2952_);
lean_ctor_set(v___x_3036_, 5, v_proof_x3f_2953_);
lean_ctor_set(v___x_3036_, 6, v_size_2955_);
lean_ctor_set(v___x_3036_, 7, v_idx_2960_);
lean_ctor_set(v___x_3036_, 8, v_generation_2961_);
lean_ctor_set(v___x_3036_, 9, v_mt_2962_);
lean_ctor_set(v___x_3036_, 10, v_sTerms_2963_);
lean_ctor_set(v___x_3036_, 11, v_ematchDiagSource_2965_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12, v_flipped_2954_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12 + 1, v_interpreted_2956_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12 + 2, v_ctor_2957_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12 + 3, v_hasLambdas_2958_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12 + 4, v_heqProofs_2959_);
lean_ctor_set_uint8(v___x_3036_, sizeof(void*)*12 + 5, v_funCC_2964_);
v___x_3037_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2949_, v___x_3036_, v___y_2931_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec_ref_known(v___x_3037_, 1);
v___x_3038_ = lean_st_ref_get(v___y_2931_);
lean_inc(v_fst_2997_);
v___x_3039_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3038_, v_fst_2997_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___x_3038_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v_self_3041_; lean_object* v_next_3042_; lean_object* v_root_3043_; lean_object* v_target_x3f_3044_; lean_object* v_proof_x3f_3045_; uint8_t v_flipped_3046_; lean_object* v_size_3047_; uint8_t v_interpreted_3048_; uint8_t v_ctor_3049_; uint8_t v_hasLambdas_3050_; uint8_t v_heqProofs_3051_; lean_object* v_idx_3052_; lean_object* v_generation_3053_; lean_object* v_mt_3054_; lean_object* v_sTerms_3055_; uint8_t v_funCC_3056_; lean_object* v_ematchDiagSource_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3073_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v_self_3041_ = lean_ctor_get(v_a_3040_, 0);
v_next_3042_ = lean_ctor_get(v_a_3040_, 1);
v_root_3043_ = lean_ctor_get(v_a_3040_, 2);
v_target_x3f_3044_ = lean_ctor_get(v_a_3040_, 4);
v_proof_x3f_3045_ = lean_ctor_get(v_a_3040_, 5);
v_flipped_3046_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12);
v_size_3047_ = lean_ctor_get(v_a_3040_, 6);
v_interpreted_3048_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12 + 1);
v_ctor_3049_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12 + 2);
v_hasLambdas_3050_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12 + 3);
v_heqProofs_3051_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12 + 4);
v_idx_3052_ = lean_ctor_get(v_a_3040_, 7);
v_generation_3053_ = lean_ctor_get(v_a_3040_, 8);
v_mt_3054_ = lean_ctor_get(v_a_3040_, 9);
v_sTerms_3055_ = lean_ctor_get(v_a_3040_, 10);
v_funCC_3056_ = lean_ctor_get_uint8(v_a_3040_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3057_ = lean_ctor_get(v_a_3040_, 11);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_a_3040_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v_a_3040_, 3);
lean_dec(v_unused_3074_);
v___x_3059_ = v_a_3040_;
v_isShared_3060_ = v_isSharedCheck_3073_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_ematchDiagSource_3057_);
lean_inc(v_sTerms_3055_);
lean_inc(v_mt_3054_);
lean_inc(v_generation_3053_);
lean_inc(v_idx_3052_);
lean_inc(v_size_3047_);
lean_inc(v_proof_x3f_3045_);
lean_inc(v_target_x3f_3044_);
lean_inc(v_root_3043_);
lean_inc(v_next_3042_);
lean_inc(v_self_3041_);
lean_dec(v_a_3040_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3073_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 3, v_self_2949_);
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_self_3041_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_next_3042_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_root_3043_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_self_2949_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_target_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v_proof_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_size_3047_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_idx_3052_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_generation_3053_);
lean_ctor_set(v_reuseFailAlloc_3072_, 9, v_mt_3054_);
lean_ctor_set(v_reuseFailAlloc_3072_, 10, v_sTerms_3055_);
lean_ctor_set(v_reuseFailAlloc_3072_, 11, v_ematchDiagSource_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12, v_flipped_3046_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 1, v_interpreted_3048_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 2, v_ctor_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 3, v_hasLambdas_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 4, v_heqProofs_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 5, v_funCC_3056_);
v___x_3062_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2997_, v___x_3062_, v___y_2931_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_dec_ref_known(v___x_3063_, 1);
goto v___jp_2969_;
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v_next_2950_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_fst_2997_);
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_self_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3075_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3039_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3039_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_fst_2997_);
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_self_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3083_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3037_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3037_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
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
lean_dec(v_fst_2997_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2969_;
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_fst_2997_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_self_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3095_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_2998_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_2998_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2969_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v___x_2985_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_self_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3103_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_2986_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_2986_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_del_object(v___x_2940_);
lean_dec(v_snd_2938_);
lean_dec_ref(v_rootNew_2928_);
v_a_3115_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_2944_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_2944_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3125_, lean_object* v_rootNew_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
uint8_t v_a_26469__boxed_3136_; lean_object* v_res_3137_; 
v_a_26469__boxed_3136_ = lean_unbox(v_a_3127_);
v_res_3137_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3125_, v_rootNew_3126_, v_a_26469__boxed_3136_, v_a_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v_lhs_3125_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3138_, lean_object* v_rootNew_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3139_, v_a_3144_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = lean_box(0);
lean_inc_ref(v_lhs_3138_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v_lhs_3138_);
v___x_3155_ = lean_unbox(v_a_3152_);
lean_dec(v_a_3152_);
v___x_3156_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3138_, v_rootNew_3139_, v___x_3155_, v___x_3154_, v_a_3140_, v_a_3144_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec_ref(v_lhs_3138_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3170_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3170_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3170_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v_fst_3161_; 
v_fst_3161_ = lean_ctor_get(v_a_3157_, 0);
lean_inc(v_fst_3161_);
lean_dec(v_a_3157_);
if (lean_obj_tag(v_fst_3161_) == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3162_ = lean_box(0);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3162_);
v___x_3164_ = v___x_3159_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
else
{
lean_object* v_val_3166_; lean_object* v___x_3168_; 
v_val_3166_ = lean_ctor_get(v_fst_3161_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v_fst_3161_, 1);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v_val_3166_);
v___x_3168_ = v___x_3159_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_val_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3156_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3156_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v_rootNew_3139_);
lean_dec_ref(v_lhs_3138_);
v_a_3179_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3151_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3151_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3187_, lean_object* v_rootNew_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3187_, v_rootNew_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec(v_a_3189_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3201_, v_x_3203_, v_x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3206_, lean_object* v_00_u03b2_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3206_, v_00_u03b2_3207_, v_x_3208_, v_x_3209_);
lean_dec_ref(v_x_3208_);
lean_dec_ref(v___x_3206_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3211_, lean_object* v_00_u03b2_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3211_, v_x_3213_, v_x_3214_, v_x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3217_, lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3217_, v_00_u03b2_3218_, v_x_3219_, v_x_3220_, v_x_3221_);
lean_dec_ref(v___x_3217_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3223_, lean_object* v_rootNew_3224_, uint8_t v_a_3225_, lean_object* v_inst_3226_, lean_object* v_a_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3223_, v_rootNew_3224_, v_a_3225_, v_a_3227_, v___y_3228_, v___y_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3240_, lean_object* v_rootNew_3241_, lean_object* v_a_3242_, lean_object* v_inst_3243_, lean_object* v_a_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_a_26854__boxed_3256_; lean_object* v_res_3257_; 
v_a_26854__boxed_3256_ = lean_unbox(v_a_3242_);
v_res_3257_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3240_, v_rootNew_3241_, v_a_26854__boxed_3256_, v_inst_3243_, v_a_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v_lhs_3240_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, size_t v_x_3261_, lean_object* v_x_3262_){
_start:
{
lean_object* v___x_3263_; 
lean_inc_ref(v_x_3260_);
v___x_3263_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3258_, v_x_3260_, v_x_3261_, v_x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_, lean_object* v_x_3268_){
_start:
{
size_t v_x_26897__boxed_3269_; lean_object* v_res_3270_; 
v_x_26897__boxed_3269_ = lean_unbox_usize(v_x_3267_);
lean_dec(v_x_3267_);
v_res_3270_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3264_, v_00_u03b2_3265_, v_x_3266_, v_x_26897__boxed_3269_, v_x_3268_);
lean_dec_ref(v_x_3266_);
lean_dec_ref(v___x_3264_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3271_, lean_object* v_00_u03b2_3272_, lean_object* v_x_3273_, size_t v_x_3274_, size_t v_x_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3271_, v_x_3273_, v_x_3274_, v_x_3275_, v_x_3276_, v_x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3279_, lean_object* v_00_u03b2_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_){
_start:
{
size_t v_x_26911__boxed_3286_; size_t v_x_26912__boxed_3287_; lean_object* v_res_3288_; 
v_x_26911__boxed_3286_ = lean_unbox_usize(v_x_3282_);
lean_dec(v_x_3282_);
v_x_26912__boxed_3287_ = lean_unbox_usize(v_x_3283_);
lean_dec(v_x_3283_);
v_res_3288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3279_, v_00_u03b2_3280_, v_x_3281_, v_x_26911__boxed_3286_, v_x_26912__boxed_3287_, v_x_3284_, v_x_3285_);
lean_dec_ref(v___x_3279_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3289_, lean_object* v_00_u03b2_3290_, lean_object* v_keys_3291_, lean_object* v_vals_3292_, lean_object* v_heq_3293_, lean_object* v_i_3294_, lean_object* v_k_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3289_, v_keys_3291_, v_vals_3292_, v_i_3294_, v_k_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3297_, lean_object* v_00_u03b2_3298_, lean_object* v_keys_3299_, lean_object* v_vals_3300_, lean_object* v_heq_3301_, lean_object* v_i_3302_, lean_object* v_k_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3297_, v_00_u03b2_3298_, v_keys_3299_, v_vals_3300_, v_heq_3301_, v_i_3302_, v_k_3303_);
lean_dec_ref(v_vals_3300_);
lean_dec_ref(v_keys_3299_);
lean_dec_ref(v___x_3297_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3305_, lean_object* v_00_u03b2_3306_, lean_object* v_n_3307_, lean_object* v_k_3308_, lean_object* v_v_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3305_, v_n_3307_, v_k_3308_, v_v_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3311_, lean_object* v_00_u03b2_3312_, lean_object* v_n_3313_, lean_object* v_k_3314_, lean_object* v_v_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3311_, v_00_u03b2_3312_, v_n_3313_, v_k_3314_, v_v_3315_);
lean_dec_ref(v___x_3311_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3317_, lean_object* v_00_u03b2_3318_, size_t v_depth_3319_, lean_object* v_keys_3320_, lean_object* v_vals_3321_, lean_object* v_heq_3322_, lean_object* v_i_3323_, lean_object* v_entries_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3317_, v_depth_3319_, v_keys_3320_, v_vals_3321_, v_i_3323_, v_entries_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3326_, lean_object* v_00_u03b2_3327_, lean_object* v_depth_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_entries_3333_){
_start:
{
size_t v_depth_boxed_3334_; lean_object* v_res_3335_; 
v_depth_boxed_3334_ = lean_unbox_usize(v_depth_3328_);
lean_dec(v_depth_3328_);
v_res_3335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3326_, v_00_u03b2_3327_, v_depth_boxed_3334_, v_keys_3329_, v_vals_3330_, v_heq_3331_, v_i_3332_, v_entries_3333_);
lean_dec_ref(v_vals_3330_);
lean_dec_ref(v_keys_3329_);
lean_dec_ref(v___x_3326_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3336_, lean_object* v_00_u03b2_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3336_, v_x_3338_, v_x_3339_, v_x_3340_, v_x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3343_, lean_object* v_00_u03b2_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3343_, v_00_u03b2_3344_, v_x_3345_, v_x_3346_, v_x_3347_, v_x_3348_);
lean_dec_ref(v___x_3343_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3350_, lean_object* v_b_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
if (lean_obj_tag(v_as_x27_3350_) == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_b_3351_);
return v___x_3363_;
}
else
{
lean_object* v_head_3364_; lean_object* v_tail_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_head_3364_ = lean_ctor_get(v_as_x27_3350_, 0);
v_tail_3365_ = lean_ctor_get(v_as_x27_3350_, 1);
v___x_3366_ = lean_box(0);
lean_inc(v_head_3364_);
v___x_3367_ = l_Lean_Meta_Grind_propagateUp(v_head_3364_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_dec_ref_known(v___x_3367_, 1);
v_as_x27_3350_ = v_tail_3365_;
v_b_3351_ = v___x_3366_;
goto _start;
}
else
{
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3369_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec(v_as_x27_3369_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3383_, lean_object* v_b_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
if (lean_obj_tag(v_as_x27_3383_) == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_b_3384_);
return v___x_3396_;
}
else
{
lean_object* v_head_3397_; lean_object* v_tail_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_head_3397_ = lean_ctor_get(v_as_x27_3383_, 0);
v_tail_3398_ = lean_ctor_get(v_as_x27_3383_, 1);
v___x_3399_ = lean_box(0);
lean_inc(v_head_3397_);
v___x_3400_ = l_Lean_Meta_Grind_propagateDown(v_head_3397_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_dec_ref_known(v___x_3400_, 1);
v_as_x27_3383_ = v_tail_3398_;
v_b_3384_ = v___x_3399_;
goto _start;
}
else
{
return v___x_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3402_, lean_object* v_b_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3402_, v_b_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v_as_x27_3402_);
return v_res_3415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_cls_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3420_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3421_ = l_Lean_Name_append(v___x_3420_, v_cls_3419_);
return v___x_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3434_, uint8_t v_isHEq_3435_, lean_object* v_lhs_3436_, lean_object* v_rhs_3437_, lean_object* v_lhsNode_3438_, lean_object* v_rhsNode_3439_, lean_object* v_lhsRoot_3440_, lean_object* v_rhsRoot_3441_, uint8_t v_flipped_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3507_; uint8_t v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; lean_object* v___y_3534_; uint8_t v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; uint8_t v___y_3595_; uint8_t v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; uint8_t v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v_toCold_3700_; lean_object* v_options_3701_; lean_object* v_inheritedTraceOptions_3702_; uint8_t v_hasTrace_3703_; lean_object* v_cls_3704_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v_fns_u2082_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v_fns_u2081_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; 
v_toCold_3700_ = lean_ctor_get(v_a_3451_, 0);
v_options_3701_ = lean_ctor_get(v_toCold_3700_, 2);
v_inheritedTraceOptions_3702_ = lean_ctor_get(v_toCold_3700_, 11);
v_hasTrace_3703_ = lean_ctor_get_uint8(v_options_3701_, sizeof(void*)*1);
v_cls_3704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3703_ == 0)
{
v___y_3824_ = v_a_3443_;
v___y_3825_ = v_a_3444_;
v___y_3826_ = v_a_3445_;
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3702_, v_options_3701_, v___x_3904_);
if (v___x_3905_ == 0)
{
v___y_3824_ = v_a_3443_;
v___y_3825_ = v_a_3444_;
v___y_3826_ = v_a_3445_;
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Meta_Grind_updateLastTag(v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3907_; 
lean_dec_ref_known(v___x_3906_, 1);
lean_inc_ref(v_lhs_3436_);
v___x_3907_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3436_, v_a_3443_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
lean_inc_ref(v_rhs_3437_);
v___x_3909_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3437_, v_a_3443_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
lean_ctor_set(v___x_3912_, 1, v_a_3908_);
v___x_3913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3912_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v_a_3910_);
v___x_3916_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3704_, v___x_3915_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_dec_ref_known(v___x_3916_, 1);
v___y_3824_ = v_a_3443_;
v___y_3825_ = v_a_3444_;
v___y_3826_ = v_a_3445_;
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
goto v___jp_3823_;
}
else
{
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhsNode_3438_);
lean_dec_ref(v_rhs_3437_);
lean_dec_ref(v_lhs_3436_);
lean_dec_ref(v_proof_3434_);
return v___x_3916_;
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_a_3908_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhsNode_3438_);
lean_dec_ref(v_rhs_3437_);
lean_dec_ref(v_lhs_3436_);
lean_dec_ref(v_proof_3434_);
v_a_3917_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3909_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3909_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhsNode_3438_);
lean_dec_ref(v_rhs_3437_);
lean_dec_ref(v_lhs_3436_);
lean_dec_ref(v_proof_3434_);
v_a_3925_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3907_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3907_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhsNode_3438_);
lean_dec_ref(v_rhs_3437_);
lean_dec_ref(v_lhs_3436_);
lean_dec_ref(v_proof_3434_);
return v___x_3906_;
}
}
}
v___jp_3454_:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3461_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3497_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3497_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3497_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_unbox(v_a_3472_);
lean_dec(v_a_3472_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_del_object(v___x_3474_);
v___x_3477_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3455_);
lean_dec(v___y_3455_);
v___x_3478_ = lean_box(0);
v___x_3479_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3477_, v___x_3478_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___x_3477_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref_known(v___x_3479_, 1);
v___x_3480_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3456_, v___x_3478_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref_known(v___x_3480_, 1);
v___x_3481_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3459_, v___y_3458_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3459_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3482_; 
lean_dec_ref_known(v___x_3481_, 1);
v___x_3482_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3457_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3491_; 
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v___x_3482_, 0);
lean_dec(v_unused_3492_);
v___x_3484_ = v___x_3482_;
v_isShared_3485_ = v_isSharedCheck_3491_;
goto v_resetjp_3483_;
}
else
{
lean_dec(v___x_3482_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3491_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
uint8_t v___x_3486_; 
v___x_3486_ = l_Lean_Expr_isTrue(v___y_3460_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v___y_3456_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3478_);
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3478_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
lean_object* v___x_3490_; 
lean_del_object(v___x_3484_);
v___x_3490_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3456_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3456_);
return v___x_3490_;
}
}
}
else
{
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3456_);
return v___x_3482_;
}
}
else
{
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
return v___x_3481_;
}
}
else
{
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
return v___x_3480_;
}
}
else
{
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
return v___x_3479_;
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
v___x_3493_ = lean_box(0);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3493_);
v___x_3495_ = v___x_3474_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
v_a_3498_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3471_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3471_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_inc_ref(v___y_3518_);
v___x_3544_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3544_, 0, v___y_3518_);
lean_ctor_set(v___x_3544_, 1, v___y_3520_);
lean_ctor_set(v___x_3544_, 2, v___y_3511_);
lean_ctor_set(v___x_3544_, 3, v___y_3525_);
lean_ctor_set(v___x_3544_, 4, v___y_3513_);
lean_ctor_set(v___x_3544_, 5, v___y_3516_);
lean_ctor_set(v___x_3544_, 6, v___y_3530_);
lean_ctor_set(v___x_3544_, 7, v___y_3542_);
lean_ctor_set(v___x_3544_, 8, v___y_3537_);
lean_ctor_set(v___x_3544_, 9, v___y_3536_);
lean_ctor_set(v___x_3544_, 10, v___y_3522_);
lean_ctor_set(v___x_3544_, 11, v___y_3534_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12, v___y_3539_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 1, v___y_3508_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 2, v___y_3535_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 3, v___y_3543_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 4, v___y_3533_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 5, v___y_3526_);
lean_inc_ref(v___y_3521_);
v___x_3545_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3521_, v___x_3544_, v___y_3538_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3545_, 1);
lean_inc_ref(v___y_3540_);
v___x_3546_ = l_Lean_Meta_Grind_propagateBeta(v___y_3540_, v___y_3512_, v___y_3538_, v___y_3514_, v___y_3507_, v___y_3541_, v___y_3519_, v___y_3515_, v___y_3529_, v___y_3527_, v___y_3510_, v___y_3509_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3546_, 1);
lean_inc_ref(v___y_3517_);
v___x_3547_ = l_Lean_Meta_Grind_propagateBeta(v___y_3517_, v___y_3532_, v___y_3538_, v___y_3514_, v___y_3507_, v___y_3541_, v___y_3519_, v___y_3515_, v___y_3529_, v___y_3527_, v___y_3510_, v___y_3509_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; 
lean_dec_ref_known(v___x_3547_, 1);
v___x_3548_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v___y_3528_, v_lhsRoot_3440_, v___y_3533_, v___y_3538_, v___y_3529_, v___y_3527_, v___y_3510_, v___y_3509_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3531_, v___y_3538_);
lean_dec_ref(v___y_3531_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3550_, 1);
lean_inc_ref(v___y_3521_);
v___x_3551_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3523_, v___y_3521_, v___y_3538_, v___y_3514_, v___y_3507_, v___y_3541_, v___y_3519_, v___y_3515_, v___y_3529_, v___y_3527_, v___y_3510_, v___y_3509_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
v___x_3552_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3538_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; uint8_t v___x_3554_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3554_ = lean_unbox(v_a_3553_);
lean_dec(v_a_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3518_, v___y_3538_, v___y_3514_, v___y_3507_, v___y_3541_, v___y_3519_, v___y_3515_, v___y_3529_, v___y_3527_, v___y_3510_, v___y_3509_);
lean_dec_ref(v___y_3518_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_dec_ref_known(v___x_3555_, 1);
v___y_3455_ = v___y_3523_;
v___y_3456_ = v___y_3524_;
v___y_3457_ = v_a_3549_;
v___y_3458_ = v___y_3517_;
v___y_3459_ = v___y_3540_;
v___y_3460_ = v___y_3521_;
v___y_3461_ = v___y_3538_;
v___y_3462_ = v___y_3514_;
v___y_3463_ = v___y_3507_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v___y_3519_;
v___y_3466_ = v___y_3515_;
v___y_3467_ = v___y_3529_;
v___y_3468_ = v___y_3527_;
v___y_3469_ = v___y_3510_;
v___y_3470_ = v___y_3509_;
goto v___jp_3454_;
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3517_);
return v___x_3555_;
}
}
else
{
lean_dec_ref(v___y_3518_);
v___y_3455_ = v___y_3523_;
v___y_3456_ = v___y_3524_;
v___y_3457_ = v_a_3549_;
v___y_3458_ = v___y_3517_;
v___y_3459_ = v___y_3540_;
v___y_3460_ = v___y_3521_;
v___y_3461_ = v___y_3538_;
v___y_3462_ = v___y_3514_;
v___y_3463_ = v___y_3507_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v___y_3519_;
v___y_3466_ = v___y_3515_;
v___y_3467_ = v___y_3529_;
v___y_3468_ = v___y_3527_;
v___y_3469_ = v___y_3510_;
v___y_3470_ = v___y_3509_;
goto v___jp_3454_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
v_a_3556_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3552_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3552_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v___x_3551_;
}
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v___x_3550_;
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
v_a_3564_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3548_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3548_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v_lhsRoot_3440_);
return v___x_3547_;
}
}
else
{
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v_lhsRoot_3440_);
return v___x_3546_;
}
}
else
{
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v_lhsRoot_3440_);
return v___x_3545_;
}
}
v___jp_3572_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_st_ref_get(v___y_3587_);
v___x_3597_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3596_, v___y_3573_, v___y_3579_, v___y_3577_, v___y_3583_, v___y_3582_);
lean_dec(v___x_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v_self_3599_; lean_object* v_root_3600_; lean_object* v_congr_3601_; lean_object* v_target_x3f_3602_; lean_object* v_proof_x3f_3603_; uint8_t v_flipped_3604_; lean_object* v_size_3605_; uint8_t v_interpreted_3606_; uint8_t v_ctor_3607_; uint8_t v_hasLambdas_3608_; lean_object* v_idx_3609_; lean_object* v_generation_3610_; lean_object* v_mt_3611_; lean_object* v_sTerms_3612_; uint8_t v_funCC_3613_; lean_object* v_ematchDiagSource_3614_; lean_object* v___x_3615_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v_self_3599_ = lean_ctor_get(v_a_3598_, 0);
lean_inc_ref(v_self_3599_);
v_root_3600_ = lean_ctor_get(v_a_3598_, 2);
lean_inc_ref(v_root_3600_);
v_congr_3601_ = lean_ctor_get(v_a_3598_, 3);
lean_inc_ref(v_congr_3601_);
v_target_x3f_3602_ = lean_ctor_get(v_a_3598_, 4);
lean_inc(v_target_x3f_3602_);
v_proof_x3f_3603_ = lean_ctor_get(v_a_3598_, 5);
lean_inc(v_proof_x3f_3603_);
v_flipped_3604_ = lean_ctor_get_uint8(v_a_3598_, sizeof(void*)*12);
v_size_3605_ = lean_ctor_get(v_a_3598_, 6);
v_interpreted_3606_ = lean_ctor_get_uint8(v_a_3598_, sizeof(void*)*12 + 1);
v_ctor_3607_ = lean_ctor_get_uint8(v_a_3598_, sizeof(void*)*12 + 2);
v_hasLambdas_3608_ = lean_ctor_get_uint8(v_a_3598_, sizeof(void*)*12 + 3);
v_idx_3609_ = lean_ctor_get(v_a_3598_, 7);
lean_inc(v_idx_3609_);
v_generation_3610_ = lean_ctor_get(v_a_3598_, 8);
lean_inc(v_generation_3610_);
v_mt_3611_ = lean_ctor_get(v_a_3598_, 9);
lean_inc(v_mt_3611_);
v_sTerms_3612_ = lean_ctor_get(v_a_3598_, 10);
lean_inc(v_sTerms_3612_);
v_funCC_3613_ = lean_ctor_get_uint8(v_a_3598_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3614_ = lean_ctor_get(v_a_3598_, 11);
lean_inc(v_ematchDiagSource_3614_);
v___x_3615_ = lean_nat_add(v_size_3605_, v___y_3593_);
lean_dec(v___y_3593_);
if (v_hasLambdas_3608_ == 0)
{
v___y_3507_ = v___y_3576_;
v___y_3508_ = v_interpreted_3606_;
v___y_3509_ = v___y_3582_;
v___y_3510_ = v___y_3583_;
v___y_3511_ = v_root_3600_;
v___y_3512_ = v___y_3584_;
v___y_3513_ = v_target_x3f_3602_;
v___y_3514_ = v___y_3585_;
v___y_3515_ = v___y_3586_;
v___y_3516_ = v_proof_x3f_3603_;
v___y_3517_ = v___y_3588_;
v___y_3518_ = v_self_3599_;
v___y_3519_ = v___y_3592_;
v___y_3520_ = v___y_3591_;
v___y_3521_ = v___y_3594_;
v___y_3522_ = v_sTerms_3612_;
v___y_3523_ = v___y_3574_;
v___y_3524_ = v___y_3575_;
v___y_3525_ = v_congr_3601_;
v___y_3526_ = v_funCC_3613_;
v___y_3527_ = v___y_3577_;
v___y_3528_ = v_a_3598_;
v___y_3529_ = v___y_3579_;
v___y_3530_ = v___x_3615_;
v___y_3531_ = v___y_3581_;
v___y_3532_ = v___y_3580_;
v___y_3533_ = v___y_3595_;
v___y_3534_ = v_ematchDiagSource_3614_;
v___y_3535_ = v_ctor_3607_;
v___y_3536_ = v_mt_3611_;
v___y_3537_ = v_generation_3610_;
v___y_3538_ = v___y_3587_;
v___y_3539_ = v_flipped_3604_;
v___y_3540_ = v___y_3589_;
v___y_3541_ = v___y_3590_;
v___y_3542_ = v_idx_3609_;
v___y_3543_ = v___y_3578_;
goto v___jp_3506_;
}
else
{
v___y_3507_ = v___y_3576_;
v___y_3508_ = v_interpreted_3606_;
v___y_3509_ = v___y_3582_;
v___y_3510_ = v___y_3583_;
v___y_3511_ = v_root_3600_;
v___y_3512_ = v___y_3584_;
v___y_3513_ = v_target_x3f_3602_;
v___y_3514_ = v___y_3585_;
v___y_3515_ = v___y_3586_;
v___y_3516_ = v_proof_x3f_3603_;
v___y_3517_ = v___y_3588_;
v___y_3518_ = v_self_3599_;
v___y_3519_ = v___y_3592_;
v___y_3520_ = v___y_3591_;
v___y_3521_ = v___y_3594_;
v___y_3522_ = v_sTerms_3612_;
v___y_3523_ = v___y_3574_;
v___y_3524_ = v___y_3575_;
v___y_3525_ = v_congr_3601_;
v___y_3526_ = v_funCC_3613_;
v___y_3527_ = v___y_3577_;
v___y_3528_ = v_a_3598_;
v___y_3529_ = v___y_3579_;
v___y_3530_ = v___x_3615_;
v___y_3531_ = v___y_3581_;
v___y_3532_ = v___y_3580_;
v___y_3533_ = v___y_3595_;
v___y_3534_ = v_ematchDiagSource_3614_;
v___y_3535_ = v_ctor_3607_;
v___y_3536_ = v_mt_3611_;
v___y_3537_ = v_generation_3610_;
v___y_3538_ = v___y_3587_;
v___y_3539_ = v_flipped_3604_;
v___y_3540_ = v___y_3589_;
v___y_3541_ = v___y_3590_;
v___y_3542_ = v_idx_3609_;
v___y_3543_ = v_hasLambdas_3608_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v_lhsRoot_3440_);
v_a_3616_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3597_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3597_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
v___jp_3624_:
{
lean_object* v___x_3647_; 
v___x_3647_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3627_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3647_) == 0)
{
uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec_ref_known(v___x_3647_, 1);
v___x_3648_ = 0;
v___x_3649_ = lean_st_ref_get(v___y_3637_);
v___x_3650_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3649_, v_lhs_3436_, v___x_3648_);
lean_dec(v___x_3649_);
v___x_3651_ = lean_st_ref_get(v___y_3637_);
lean_inc_ref(v___y_3634_);
v___x_3652_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3651_, v___y_3634_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___x_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v_self_3654_; lean_object* v_root_3655_; lean_object* v_congr_3656_; lean_object* v_target_x3f_3657_; lean_object* v_proof_x3f_3658_; uint8_t v_flipped_3659_; lean_object* v_size_3660_; uint8_t v_interpreted_3661_; uint8_t v_ctor_3662_; uint8_t v_hasLambdas_3663_; uint8_t v_heqProofs_3664_; lean_object* v_idx_3665_; lean_object* v_generation_3666_; lean_object* v_mt_3667_; lean_object* v_sTerms_3668_; uint8_t v_funCC_3669_; lean_object* v_ematchDiagSource_3670_; lean_object* v_self_3671_; lean_object* v_next_3672_; uint8_t v_heqProofs_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3681_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v_self_3654_ = lean_ctor_get(v_a_3653_, 0);
lean_inc_ref(v_self_3654_);
v_root_3655_ = lean_ctor_get(v_a_3653_, 2);
lean_inc_ref(v_root_3655_);
v_congr_3656_ = lean_ctor_get(v_a_3653_, 3);
lean_inc_ref(v_congr_3656_);
v_target_x3f_3657_ = lean_ctor_get(v_a_3653_, 4);
lean_inc(v_target_x3f_3657_);
v_proof_x3f_3658_ = lean_ctor_get(v_a_3653_, 5);
lean_inc(v_proof_x3f_3658_);
v_flipped_3659_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12);
v_size_3660_ = lean_ctor_get(v_a_3653_, 6);
lean_inc(v_size_3660_);
v_interpreted_3661_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12 + 1);
v_ctor_3662_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12 + 2);
v_hasLambdas_3663_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12 + 3);
v_heqProofs_3664_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12 + 4);
v_idx_3665_ = lean_ctor_get(v_a_3653_, 7);
lean_inc(v_idx_3665_);
v_generation_3666_ = lean_ctor_get(v_a_3653_, 8);
lean_inc(v_generation_3666_);
v_mt_3667_ = lean_ctor_get(v_a_3653_, 9);
lean_inc(v_mt_3667_);
v_sTerms_3668_ = lean_ctor_get(v_a_3653_, 10);
lean_inc(v_sTerms_3668_);
v_funCC_3669_ = lean_ctor_get_uint8(v_a_3653_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3670_ = lean_ctor_get(v_a_3653_, 11);
lean_inc(v_ematchDiagSource_3670_);
lean_dec(v_a_3653_);
v_self_3671_ = lean_ctor_get(v_rhsRoot_3441_, 0);
v_next_3672_ = lean_ctor_get(v_rhsRoot_3441_, 1);
v_heqProofs_3673_ = lean_ctor_get_uint8(v_rhsRoot_3441_, sizeof(void*)*12 + 4);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_rhsRoot_3441_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; lean_object* v_unused_3683_; lean_object* v_unused_3684_; lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; lean_object* v_unused_3688_; lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; 
v_unused_3682_ = lean_ctor_get(v_rhsRoot_3441_, 11);
lean_dec(v_unused_3682_);
v_unused_3683_ = lean_ctor_get(v_rhsRoot_3441_, 10);
lean_dec(v_unused_3683_);
v_unused_3684_ = lean_ctor_get(v_rhsRoot_3441_, 9);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_rhsRoot_3441_, 8);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_rhsRoot_3441_, 7);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_rhsRoot_3441_, 6);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_rhsRoot_3441_, 5);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_rhsRoot_3441_, 4);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_rhsRoot_3441_, 3);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_rhsRoot_3441_, 2);
lean_dec(v_unused_3691_);
v___x_3675_ = v_rhsRoot_3441_;
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_next_3672_);
lean_inc(v_self_3671_);
lean_dec(v_rhsRoot_3441_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 11, v_ematchDiagSource_3670_);
lean_ctor_set(v___x_3675_, 10, v_sTerms_3668_);
lean_ctor_set(v___x_3675_, 9, v_mt_3667_);
lean_ctor_set(v___x_3675_, 8, v_generation_3666_);
lean_ctor_set(v___x_3675_, 7, v_idx_3665_);
lean_ctor_set(v___x_3675_, 6, v_size_3660_);
lean_ctor_set(v___x_3675_, 5, v_proof_x3f_3658_);
lean_ctor_set(v___x_3675_, 4, v_target_x3f_3657_);
lean_ctor_set(v___x_3675_, 3, v_congr_3656_);
lean_ctor_set(v___x_3675_, 2, v_root_3655_);
lean_ctor_set(v___x_3675_, 0, v_self_3654_);
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_self_3654_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_next_3672_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_root_3655_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_congr_3656_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_target_x3f_3657_);
lean_ctor_set(v_reuseFailAlloc_3680_, 5, v_proof_x3f_3658_);
lean_ctor_set(v_reuseFailAlloc_3680_, 6, v_size_3660_);
lean_ctor_set(v_reuseFailAlloc_3680_, 7, v_idx_3665_);
lean_ctor_set(v_reuseFailAlloc_3680_, 8, v_generation_3666_);
lean_ctor_set(v_reuseFailAlloc_3680_, 9, v_mt_3667_);
lean_ctor_set(v_reuseFailAlloc_3680_, 10, v_sTerms_3668_);
lean_ctor_set(v_reuseFailAlloc_3680_, 11, v_ematchDiagSource_3670_);
v___x_3678_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; 
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12, v_flipped_3659_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12 + 1, v_interpreted_3661_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12 + 2, v_ctor_3662_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12 + 3, v_hasLambdas_3663_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12 + 4, v_heqProofs_3664_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*12 + 5, v_funCC_3669_);
v___x_3679_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3630_, v___x_3678_, v___y_3637_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_dec_ref_known(v___x_3679_, 1);
if (v_isHEq_3435_ == 0)
{
if (v_heqProofs_3673_ == 0)
{
v___y_3573_ = v_self_3671_;
v___y_3574_ = v___y_3627_;
v___y_3575_ = v___x_3650_;
v___y_3576_ = v___y_3639_;
v___y_3577_ = v___y_3644_;
v___y_3578_ = v___y_3629_;
v___y_3579_ = v___y_3643_;
v___y_3580_ = v___y_3633_;
v___y_3581_ = v___y_3634_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3645_;
v___y_3584_ = v___y_3626_;
v___y_3585_ = v___y_3638_;
v___y_3586_ = v___y_3642_;
v___y_3587_ = v___y_3637_;
v___y_3588_ = v___y_3628_;
v___y_3589_ = v___y_3631_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3632_;
v___y_3592_ = v___y_3641_;
v___y_3593_ = v___y_3635_;
v___y_3594_ = v___y_3636_;
v___y_3595_ = v___y_3625_;
goto v___jp_3572_;
}
else
{
v___y_3573_ = v_self_3671_;
v___y_3574_ = v___y_3627_;
v___y_3575_ = v___x_3650_;
v___y_3576_ = v___y_3639_;
v___y_3577_ = v___y_3644_;
v___y_3578_ = v___y_3629_;
v___y_3579_ = v___y_3643_;
v___y_3580_ = v___y_3633_;
v___y_3581_ = v___y_3634_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3645_;
v___y_3584_ = v___y_3626_;
v___y_3585_ = v___y_3638_;
v___y_3586_ = v___y_3642_;
v___y_3587_ = v___y_3637_;
v___y_3588_ = v___y_3628_;
v___y_3589_ = v___y_3631_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3632_;
v___y_3592_ = v___y_3641_;
v___y_3593_ = v___y_3635_;
v___y_3594_ = v___y_3636_;
v___y_3595_ = v_heqProofs_3673_;
goto v___jp_3572_;
}
}
else
{
v___y_3573_ = v_self_3671_;
v___y_3574_ = v___y_3627_;
v___y_3575_ = v___x_3650_;
v___y_3576_ = v___y_3639_;
v___y_3577_ = v___y_3644_;
v___y_3578_ = v___y_3629_;
v___y_3579_ = v___y_3643_;
v___y_3580_ = v___y_3633_;
v___y_3581_ = v___y_3634_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3645_;
v___y_3584_ = v___y_3626_;
v___y_3585_ = v___y_3638_;
v___y_3586_ = v___y_3642_;
v___y_3587_ = v___y_3637_;
v___y_3588_ = v___y_3628_;
v___y_3589_ = v___y_3631_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3632_;
v___y_3592_ = v___y_3641_;
v___y_3593_ = v___y_3635_;
v___y_3594_ = v___y_3636_;
v___y_3595_ = v_isHEq_3435_;
goto v___jp_3572_;
}
}
else
{
lean_dec_ref(v_self_3671_);
lean_dec(v___x_3650_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_lhsRoot_3440_);
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v___x_3650_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
v_a_3692_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3652_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3652_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
return v___x_3647_;
}
}
v___jp_3705_:
{
lean_object* v_self_3721_; lean_object* v_next_3722_; lean_object* v_size_3723_; uint8_t v_hasLambdas_3724_; uint8_t v_heqProofs_3725_; lean_object* v___x_3726_; 
v_self_3721_ = lean_ctor_get(v_lhsRoot_3440_, 0);
v_next_3722_ = lean_ctor_get(v_lhsRoot_3440_, 1);
v_size_3723_ = lean_ctor_get(v_lhsRoot_3440_, 6);
v_hasLambdas_3724_ = lean_ctor_get_uint8(v_lhsRoot_3440_, sizeof(void*)*12 + 3);
v_heqProofs_3725_ = lean_ctor_get_uint8(v_lhsRoot_3440_, sizeof(void*)*12 + 4);
v___x_3726_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3721_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v_root_3728_; lean_object* v___x_3729_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v_root_3728_ = lean_ctor_get(v_rhsNode_3439_, 2);
lean_inc_ref_n(v_root_3728_, 2);
lean_dec_ref(v_rhsNode_3439_);
lean_inc_ref(v_lhs_3436_);
v___x_3729_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3436_, v_root_3728_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_toCold_3730_; lean_object* v_options_3731_; uint8_t v_hasTrace_3732_; 
lean_dec_ref_known(v___x_3729_, 1);
v_toCold_3730_ = lean_ctor_get(v___y_3719_, 0);
v_options_3731_ = lean_ctor_get(v_toCold_3730_, 2);
v_hasTrace_3732_ = lean_ctor_get_uint8(v_options_3731_, sizeof(void*)*1);
if (v_hasTrace_3732_ == 0)
{
lean_inc(v_size_3723_);
lean_inc_ref(v_self_3721_);
lean_inc_ref(v_next_3722_);
v___y_3625_ = v_heqProofs_3725_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v_a_3727_;
v___y_3628_ = v___y_3707_;
v___y_3629_ = v_hasLambdas_3724_;
v___y_3630_ = v___y_3708_;
v___y_3631_ = v___y_3709_;
v___y_3632_ = v_next_3722_;
v___y_3633_ = v_fns_u2082_3710_;
v___y_3634_ = v_self_3721_;
v___y_3635_ = v_size_3723_;
v___y_3636_ = v_root_3728_;
v___y_3637_ = v___y_3711_;
v___y_3638_ = v___y_3712_;
v___y_3639_ = v___y_3713_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
goto v___jp_3624_;
}
else
{
lean_object* v_inheritedTraceOptions_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_inheritedTraceOptions_3733_ = lean_ctor_get(v_toCold_3730_, 11);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3733_, v_options_3731_, v___x_3734_);
if (v___x_3735_ == 0)
{
lean_inc(v_size_3723_);
lean_inc_ref(v_self_3721_);
lean_inc_ref(v_next_3722_);
v___y_3625_ = v_heqProofs_3725_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v_a_3727_;
v___y_3628_ = v___y_3707_;
v___y_3629_ = v_hasLambdas_3724_;
v___y_3630_ = v___y_3708_;
v___y_3631_ = v___y_3709_;
v___y_3632_ = v_next_3722_;
v___y_3633_ = v_fns_u2082_3710_;
v___y_3634_ = v_self_3721_;
v___y_3635_ = v_size_3723_;
v___y_3636_ = v_root_3728_;
v___y_3637_ = v___y_3711_;
v___y_3638_ = v___y_3712_;
v___y_3639_ = v___y_3713_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
goto v___jp_3624_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Meta_Grind_updateLastTag(v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v___x_3737_; 
lean_dec_ref_known(v___x_3736_, 1);
lean_inc_ref(v_lhs_3436_);
v___x_3737_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3436_, v___y_3711_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
lean_inc_ref(v_root_3728_);
v___x_3739_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3728_, v___y_3711_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = lean_st_ref_get(v___y_3711_);
lean_inc_ref(v_lhs_3436_);
v___x_3742_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3741_, v_lhs_3436_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___x_3741_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3743_, v___y_3711_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
v___x_3746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v_a_3738_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v_a_3740_);
v___x_3749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v_a_3745_);
v___x_3752_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3704_, v___x_3751_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_dec_ref_known(v___x_3752_, 1);
lean_inc(v_size_3723_);
lean_inc_ref(v_self_3721_);
lean_inc_ref(v_next_3722_);
v___y_3625_ = v_heqProofs_3725_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v_a_3727_;
v___y_3628_ = v___y_3707_;
v___y_3629_ = v_hasLambdas_3724_;
v___y_3630_ = v___y_3708_;
v___y_3631_ = v___y_3709_;
v___y_3632_ = v_next_3722_;
v___y_3633_ = v_fns_u2082_3710_;
v___y_3634_ = v_self_3721_;
v___y_3635_ = v_size_3723_;
v___y_3636_ = v_root_3728_;
v___y_3637_ = v___y_3711_;
v___y_3638_ = v___y_3712_;
v___y_3639_ = v___y_3713_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
goto v___jp_3624_;
}
else
{
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
return v___x_3752_;
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v_a_3740_);
lean_dec(v_a_3738_);
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
v_a_3753_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3744_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3744_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3740_);
lean_dec(v_a_3738_);
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
v_a_3761_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3742_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3742_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec(v_a_3738_);
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
v_a_3769_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3739_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3739_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
v_a_3777_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3737_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3737_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
return v___x_3736_;
}
}
}
}
else
{
lean_dec_ref(v_root_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_lhs_3436_);
return v___x_3729_;
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v_fns_u2082_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
v_a_3785_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3726_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3726_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
v___jp_3793_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3808_ = lean_array_get_size(v___y_3794_);
v___x_3809_ = lean_unsigned_to_nat(0u);
v___x_3810_ = lean_nat_dec_eq(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v_self_3811_; lean_object* v___x_3812_; 
v_self_3811_ = lean_ctor_get(v_lhsRoot_3440_, 0);
lean_inc_ref(v_self_3811_);
v___x_3812_ = l_Lean_Meta_Grind_getFnRoots(v_self_3811_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___y_3706_ = v_fns_u2081_3797_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v_fns_u2082_3710_ = v_a_3813_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
v___y_3719_ = v___y_3806_;
v___y_3720_ = v___y_3807_;
goto v___jp_3705_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v_fns_u2081_3797_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
v_a_3814_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3812_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3812_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
v___x_3822_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3706_ = v_fns_u2081_3797_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v_fns_u2082_3710_ = v___x_3822_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v___y_3713_ = v___y_3800_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
v___y_3719_ = v___y_3806_;
v___y_3720_ = v___y_3807_;
goto v___jp_3705_;
}
}
v___jp_3823_:
{
lean_object* v___x_3834_; 
lean_inc_ref(v_lhs_3436_);
v___x_3834_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3436_, v___y_3824_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3902_; 
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3902_ == 0)
{
lean_object* v_unused_3903_; 
v_unused_3903_ = lean_ctor_get(v___x_3834_, 0);
lean_dec(v_unused_3903_);
v___x_3836_ = v___x_3834_;
v_isShared_3837_ = v_isSharedCheck_3902_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v___x_3834_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3902_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_self_3838_; lean_object* v_next_3839_; lean_object* v_root_3840_; lean_object* v_congr_3841_; lean_object* v_size_3842_; uint8_t v_interpreted_3843_; uint8_t v_ctor_3844_; uint8_t v_hasLambdas_3845_; uint8_t v_heqProofs_3846_; lean_object* v_idx_3847_; lean_object* v_generation_3848_; lean_object* v_mt_3849_; lean_object* v_sTerms_3850_; uint8_t v_funCC_3851_; lean_object* v_ematchDiagSource_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3899_; 
v_self_3838_ = lean_ctor_get(v_lhsNode_3438_, 0);
v_next_3839_ = lean_ctor_get(v_lhsNode_3438_, 1);
v_root_3840_ = lean_ctor_get(v_lhsNode_3438_, 2);
v_congr_3841_ = lean_ctor_get(v_lhsNode_3438_, 3);
v_size_3842_ = lean_ctor_get(v_lhsNode_3438_, 6);
v_interpreted_3843_ = lean_ctor_get_uint8(v_lhsNode_3438_, sizeof(void*)*12 + 1);
v_ctor_3844_ = lean_ctor_get_uint8(v_lhsNode_3438_, sizeof(void*)*12 + 2);
v_hasLambdas_3845_ = lean_ctor_get_uint8(v_lhsNode_3438_, sizeof(void*)*12 + 3);
v_heqProofs_3846_ = lean_ctor_get_uint8(v_lhsNode_3438_, sizeof(void*)*12 + 4);
v_idx_3847_ = lean_ctor_get(v_lhsNode_3438_, 7);
v_generation_3848_ = lean_ctor_get(v_lhsNode_3438_, 8);
v_mt_3849_ = lean_ctor_get(v_lhsNode_3438_, 9);
v_sTerms_3850_ = lean_ctor_get(v_lhsNode_3438_, 10);
v_funCC_3851_ = lean_ctor_get_uint8(v_lhsNode_3438_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3852_ = lean_ctor_get(v_lhsNode_3438_, 11);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_lhsNode_3438_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; lean_object* v_unused_3901_; 
v_unused_3900_ = lean_ctor_get(v_lhsNode_3438_, 5);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_lhsNode_3438_, 4);
lean_dec(v_unused_3901_);
v___x_3854_ = v_lhsNode_3438_;
v_isShared_3855_ = v_isSharedCheck_3899_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_ematchDiagSource_3852_);
lean_inc(v_sTerms_3850_);
lean_inc(v_mt_3849_);
lean_inc(v_generation_3848_);
lean_inc(v_idx_3847_);
lean_inc(v_size_3842_);
lean_inc(v_congr_3841_);
lean_inc(v_root_3840_);
lean_inc(v_next_3839_);
lean_inc(v_self_3838_);
lean_dec(v_lhsNode_3438_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3899_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set_tag(v___x_3836_, 1);
lean_ctor_set(v___x_3836_, 0, v_rhs_3437_);
v___x_3857_ = v___x_3836_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_rhs_3437_);
v___x_3857_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_proof_3434_);
lean_inc_ref(v_root_3840_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 5, v___x_3858_);
lean_ctor_set(v___x_3854_, 4, v___x_3857_);
v___x_3860_ = v___x_3854_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_self_3838_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_next_3839_);
lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_root_3840_);
lean_ctor_set(v_reuseFailAlloc_3897_, 3, v_congr_3841_);
lean_ctor_set(v_reuseFailAlloc_3897_, 4, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3897_, 5, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3897_, 6, v_size_3842_);
lean_ctor_set(v_reuseFailAlloc_3897_, 7, v_idx_3847_);
lean_ctor_set(v_reuseFailAlloc_3897_, 8, v_generation_3848_);
lean_ctor_set(v_reuseFailAlloc_3897_, 9, v_mt_3849_);
lean_ctor_set(v_reuseFailAlloc_3897_, 10, v_sTerms_3850_);
lean_ctor_set(v_reuseFailAlloc_3897_, 11, v_ematchDiagSource_3852_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*12 + 1, v_interpreted_3843_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*12 + 2, v_ctor_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*12 + 3, v_hasLambdas_3845_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*12 + 4, v_heqProofs_3846_);
lean_ctor_set_uint8(v_reuseFailAlloc_3897_, sizeof(void*)*12 + 5, v_funCC_3851_);
v___x_3860_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
lean_ctor_set_uint8(v___x_3860_, sizeof(void*)*12, v_flipped_3442_);
lean_inc_ref(v_lhs_3436_);
v___x_3861_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3436_, v___x_3860_, v___y_3824_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3862_; 
lean_dec_ref_known(v___x_3861_, 1);
v___x_3862_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3440_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___x_3864_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3441_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = lean_array_get_size(v_a_3863_);
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = lean_nat_dec_eq(v___x_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v_self_3869_; lean_object* v___x_3870_; 
v_self_3869_ = lean_ctor_get(v_rhsRoot_3441_, 0);
lean_inc_ref(v_self_3869_);
v___x_3870_ = l_Lean_Meta_Grind_getFnRoots(v_self_3869_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3794_ = v_a_3865_;
v___y_3795_ = v_root_3840_;
v___y_3796_ = v_a_3863_;
v_fns_u2081_3797_ = v_a_3871_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
v___y_3806_ = v___y_3832_;
v___y_3807_ = v___y_3833_;
goto v___jp_3793_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_a_3865_);
lean_dec(v_a_3863_);
lean_dec_ref(v_root_3840_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
v_a_3872_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3870_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3870_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v___x_3880_; 
v___x_3880_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3794_ = v_a_3865_;
v___y_3795_ = v_root_3840_;
v___y_3796_ = v_a_3863_;
v_fns_u2081_3797_ = v___x_3880_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___y_3826_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
v___y_3806_ = v___y_3832_;
v___y_3807_ = v___y_3833_;
goto v___jp_3793_;
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3863_);
lean_dec_ref(v_root_3840_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
v_a_3881_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3864_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3864_);
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
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_root_3840_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
v_a_3889_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3862_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3862_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_dec_ref(v_root_3840_);
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhs_3436_);
return v___x_3861_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3441_);
lean_dec_ref(v_lhsRoot_3440_);
lean_dec_ref(v_rhsNode_3439_);
lean_dec_ref(v_lhsNode_3438_);
lean_dec_ref(v_rhs_3437_);
lean_dec_ref(v_lhs_3436_);
lean_dec_ref(v_proof_3434_);
return v___x_3834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3933_ = _args[0];
lean_object* v_isHEq_3934_ = _args[1];
lean_object* v_lhs_3935_ = _args[2];
lean_object* v_rhs_3936_ = _args[3];
lean_object* v_lhsNode_3937_ = _args[4];
lean_object* v_rhsNode_3938_ = _args[5];
lean_object* v_lhsRoot_3939_ = _args[6];
lean_object* v_rhsRoot_3940_ = _args[7];
lean_object* v_flipped_3941_ = _args[8];
lean_object* v_a_3942_ = _args[9];
lean_object* v_a_3943_ = _args[10];
lean_object* v_a_3944_ = _args[11];
lean_object* v_a_3945_ = _args[12];
lean_object* v_a_3946_ = _args[13];
lean_object* v_a_3947_ = _args[14];
lean_object* v_a_3948_ = _args[15];
lean_object* v_a_3949_ = _args[16];
lean_object* v_a_3950_ = _args[17];
lean_object* v_a_3951_ = _args[18];
lean_object* v_a_3952_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3953_; uint8_t v_flipped_boxed_3954_; lean_object* v_res_3955_; 
v_isHEq_boxed_3953_ = lean_unbox(v_isHEq_3934_);
v_flipped_boxed_3954_ = lean_unbox(v_flipped_3941_);
v_res_3955_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3933_, v_isHEq_boxed_3953_, v_lhs_3935_, v_rhs_3936_, v_lhsNode_3937_, v_rhsNode_3938_, v_lhsRoot_3939_, v_rhsRoot_3940_, v_flipped_boxed_3954_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec(v_a_3942_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3956_, lean_object* v_as_x27_3957_, lean_object* v_b_3958_, lean_object* v_a_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3957_, v_b_3958_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3972_, lean_object* v_as_x27_3973_, lean_object* v_b_3974_, lean_object* v_a_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3972_, v_as_x27_3973_, v_b_3974_, v_a_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec(v_as_x27_3973_);
lean_dec(v_as_3972_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3988_, lean_object* v_as_x27_3989_, lean_object* v_b_3990_, lean_object* v_a_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3989_, v_b_3990_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4004_, lean_object* v_as_x27_4005_, lean_object* v_b_4006_, lean_object* v_a_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4004_, v_as_x27_4005_, v_b_4006_, v_a_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec(v_as_x27_4005_);
lean_dec(v_as_4004_);
return v_res_4019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4022_ = l_Lean_stringToMessageData(v___x_4021_);
return v___x_4022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4028_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4029_ = l_Lean_Name_append(v___x_4028_, v___x_4027_);
return v___x_4029_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4032_ = l_Lean_stringToMessageData(v___x_4031_);
return v___x_4032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4036_, lean_object* v_rhs_4037_, lean_object* v_proof_4038_, uint8_t v_isHEq_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_st_ref_get(v_a_4040_);
lean_inc_ref(v_lhs_4036_);
v___x_4055_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4054_, v_lhs_4036_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v___x_4054_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = lean_st_ref_get(v_a_4040_);
lean_inc_ref(v_rhs_4037_);
v___x_4058_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4057_, v_rhs_4037_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v___x_4057_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v_root_4060_; lean_object* v_root_4061_; size_t v___x_4062_; size_t v___x_4063_; uint8_t v___x_4064_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v_root_4060_ = lean_ctor_get(v_a_4056_, 2);
v_root_4061_ = lean_ctor_get(v_a_4059_, 2);
v___x_4062_ = lean_ptr_addr(v_root_4060_);
v___x_4063_ = lean_ptr_addr(v_root_4061_);
v___x_4064_ = lean_usize_dec_eq(v___x_4062_, v___x_4063_);
if (v___x_4064_ == 0)
{
lean_object* v_toCold_4065_; lean_object* v_options_4066_; lean_object* v_inheritedTraceOptions_4067_; uint8_t v_hasTrace_4068_; uint8_t v___x_4069_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4135_; lean_object* v___y_4136_; uint8_t v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4165_; lean_object* v___y_4166_; uint8_t v___y_4167_; uint8_t v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; uint8_t v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; uint8_t v___y_4194_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; uint8_t v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; uint8_t v___y_4210_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v_size_4225_; uint8_t v_interpreted_4226_; uint8_t v_ctor_4227_; lean_object* v___y_4228_; uint8_t v___y_4229_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; uint8_t v_ctor_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; uint8_t v___y_4247_; lean_object* v___y_4255_; lean_object* v___y_4256_; uint8_t v_valueInconsistency_4257_; uint8_t v_trueEqFalse_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; 
v_toCold_4065_ = lean_ctor_get(v_a_4048_, 0);
v_options_4066_ = lean_ctor_get(v_toCold_4065_, 2);
v_inheritedTraceOptions_4067_ = lean_ctor_get(v_toCold_4065_, 11);
v_hasTrace_4068_ = lean_ctor_get_uint8(v_options_4066_, sizeof(void*)*1);
v___x_4069_ = 1;
if (v_hasTrace_4068_ == 0)
{
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
v___y_4322_ = v_a_4048_;
v___y_4323_ = v_a_4049_;
goto v___jp_4313_;
}
else
{
lean_object* v___x_4357_; lean_object* v_____do__lift_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4373_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4067_, v_options_4066_, v___x_4372_);
if (v___x_4373_ == 0)
{
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
v___y_4322_ = v_a_4048_;
v___y_4323_ = v_a_4049_;
goto v___jp_4313_;
}
else
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_Meta_Grind_updateLastTag(v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_dec_ref_known(v___x_4374_, 1);
if (v_isHEq_4039_ == 0)
{
lean_object* v___x_4375_; 
lean_inc_ref(v_rhs_4037_);
lean_inc_ref(v_lhs_4036_);
v___x_4375_ = l_Lean_Meta_mkEq(v_lhs_4036_, v_rhs_4037_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v_____do__lift_4359_ = v_a_4376_;
v___y_4360_ = v_a_4040_;
v___y_4361_ = v_a_4041_;
v___y_4362_ = v_a_4042_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
v___y_4368_ = v_a_4048_;
v___y_4369_ = v_a_4049_;
goto v___jp_4358_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4377_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4375_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4375_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
else
{
lean_object* v___x_4385_; 
lean_inc_ref(v_rhs_4037_);
lean_inc_ref(v_lhs_4036_);
v___x_4385_ = l_Lean_Meta_mkHEq(v_lhs_4036_, v_rhs_4037_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v_____do__lift_4359_ = v_a_4386_;
v___y_4360_ = v_a_4040_;
v___y_4361_ = v_a_4041_;
v___y_4362_ = v_a_4042_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
v___y_4368_ = v_a_4048_;
v___y_4369_ = v_a_4049_;
goto v___jp_4358_;
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4387_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4385_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4385_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
else
{
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
return v___x_4374_;
}
}
v___jp_4358_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = l_Lean_MessageData_ofExpr(v_____do__lift_4359_);
v___x_4371_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4357_, v___x_4370_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_dec_ref_known(v___x_4371_, 1);
v___y_4314_ = v___y_4360_;
v___y_4315_ = v___y_4361_;
v___y_4316_ = v___y_4362_;
v___y_4317_ = v___y_4363_;
v___y_4318_ = v___y_4364_;
v___y_4319_ = v___y_4365_;
v___y_4320_ = v___y_4366_;
v___y_4321_ = v___y_4367_;
v___y_4322_ = v___y_4368_;
v___y_4323_ = v___y_4369_;
goto v___jp_4313_;
}
else
{
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
return v___x_4371_;
}
}
}
v___jp_4070_:
{
lean_object* v_toCold_4081_; lean_object* v_options_4082_; uint8_t v_hasTrace_4083_; 
v_toCold_4081_ = lean_ctor_get(v___y_4079_, 0);
v_options_4082_ = lean_ctor_get(v_toCold_4081_, 2);
v_hasTrace_4083_ = lean_ctor_get_uint8(v_options_4082_, sizeof(void*)*1);
if (v_hasTrace_4083_ == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Meta_Grind_checkInvariants(v___x_4064_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4084_;
}
else
{
lean_object* v_inheritedTraceOptions_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; 
v_inheritedTraceOptions_4085_ = lean_ctor_get(v_toCold_4081_, 11);
v___x_4086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4087_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4088_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4085_, v_options_4082_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_Meta_Grind_checkInvariants(v___x_4064_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4089_;
}
else
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_Meta_Grind_updateLastTag(v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_dec_ref_known(v___x_4090_, 1);
v___x_4091_ = lean_st_ref_get(v___y_4071_);
v___x_4092_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4091_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___x_4091_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
v___x_4094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v_a_4093_);
v___x_4096_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4086_, v___x_4095_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; 
lean_dec_ref_known(v___x_4096_, 1);
v___x_4097_ = l_Lean_Meta_Grind_checkInvariants(v___x_4064_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4097_;
}
else
{
return v___x_4096_;
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
v_a_4098_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4092_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4092_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
return v___x_4090_;
}
}
}
}
v___jp_4106_:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4110_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; uint8_t v___x_4122_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v___x_4122_ = lean_unbox(v_a_4121_);
lean_dec(v_a_4121_);
if (v___x_4122_ == 0)
{
if (v___y_4109_ == 0)
{
lean_dec_ref(v___y_4108_);
lean_dec_ref(v___y_4107_);
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
goto v___jp_4070_;
}
else
{
lean_object* v_self_4123_; lean_object* v_self_4124_; lean_object* v___x_4125_; 
v_self_4123_ = lean_ctor_get(v___y_4107_, 0);
lean_inc_ref(v_self_4123_);
lean_dec_ref(v___y_4107_);
v_self_4124_ = lean_ctor_get(v___y_4108_, 0);
lean_inc_ref(v_self_4124_);
lean_dec_ref(v___y_4108_);
v___x_4125_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4123_, v_self_4124_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_dec_ref_known(v___x_4125_, 1);
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
goto v___jp_4070_;
}
else
{
return v___x_4125_;
}
}
}
else
{
lean_dec_ref(v___y_4108_);
lean_dec_ref(v___y_4107_);
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
v___y_4073_ = v___y_4112_;
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
goto v___jp_4070_;
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v___y_4108_);
lean_dec_ref(v___y_4107_);
v_a_4126_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4120_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4120_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
v___jp_4134_:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4138_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; uint8_t v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = lean_unbox(v_a_4149_);
lean_dec(v_a_4149_);
if (v___x_4150_ == 0)
{
uint8_t v_ctor_4151_; 
v_ctor_4151_ = lean_ctor_get_uint8(v___y_4135_, sizeof(void*)*12 + 2);
if (v_ctor_4151_ == 0)
{
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
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
goto v___jp_4106_;
}
else
{
uint8_t v_ctor_4152_; 
v_ctor_4152_ = lean_ctor_get_uint8(v___y_4136_, sizeof(void*)*12 + 2);
if (v_ctor_4152_ == 0)
{
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
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
goto v___jp_4106_;
}
else
{
lean_object* v_self_4153_; lean_object* v_self_4154_; lean_object* v___x_4155_; 
v_self_4153_ = lean_ctor_get(v___y_4135_, 0);
v_self_4154_ = lean_ctor_get(v___y_4136_, 0);
lean_inc_ref(v_self_4154_);
lean_inc_ref(v_self_4153_);
v___x_4155_ = l_Lean_Meta_Grind_propagateCtor(v_self_4153_, v_self_4154_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_dec_ref_known(v___x_4155_, 1);
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
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
goto v___jp_4106_;
}
else
{
lean_dec_ref(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v___x_4155_;
}
}
}
}
else
{
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
v___y_4118_ = v___y_4146_;
v___y_4119_ = v___y_4147_;
goto v___jp_4106_;
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v___y_4136_);
lean_dec_ref(v___y_4135_);
v_a_4156_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4148_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4148_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
v___jp_4164_:
{
if (v___y_4168_ == 0)
{
v___y_4135_ = v___y_4165_;
v___y_4136_ = v___y_4166_;
v___y_4137_ = v___y_4167_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
goto v___jp_4134_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref_known(v___x_4179_, 1);
v___y_4135_ = v___y_4165_;
v___y_4136_ = v___y_4166_;
v___y_4137_ = v___y_4167_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
v___y_4140_ = v___y_4171_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
goto v___jp_4134_;
}
else
{
lean_dec_ref(v___y_4166_);
lean_dec_ref(v___y_4165_);
return v___x_4179_;
}
}
}
v___jp_4180_:
{
lean_object* v___x_4195_; 
lean_inc_ref(v___y_4191_);
lean_inc_ref(v___y_4192_);
v___x_4195_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4038_, v_isHEq_4039_, v_rhs_4037_, v_lhs_4036_, v_a_4059_, v_a_4056_, v___y_4192_, v___y_4191_, v___x_4069_, v___y_4189_, v___y_4182_, v___y_4186_, v___y_4190_, v___y_4193_, v___y_4188_, v___y_4184_, v___y_4181_, v___y_4183_, v___y_4185_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_dec_ref_known(v___x_4195_, 1);
v___y_4165_ = v___y_4191_;
v___y_4166_ = v___y_4192_;
v___y_4167_ = v___y_4187_;
v___y_4168_ = v___y_4194_;
v___y_4169_ = v___y_4189_;
v___y_4170_ = v___y_4182_;
v___y_4171_ = v___y_4186_;
v___y_4172_ = v___y_4190_;
v___y_4173_ = v___y_4193_;
v___y_4174_ = v___y_4188_;
v___y_4175_ = v___y_4184_;
v___y_4176_ = v___y_4181_;
v___y_4177_ = v___y_4183_;
v___y_4178_ = v___y_4185_;
goto v___jp_4164_;
}
else
{
lean_dec_ref(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v___x_4195_;
}
}
v___jp_4196_:
{
lean_object* v___x_4211_; 
lean_inc_ref(v___y_4208_);
lean_inc_ref(v___y_4207_);
v___x_4211_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4038_, v_isHEq_4039_, v_lhs_4036_, v_rhs_4037_, v_a_4056_, v_a_4059_, v___y_4207_, v___y_4208_, v___x_4064_, v___y_4205_, v___y_4198_, v___y_4202_, v___y_4206_, v___y_4209_, v___y_4204_, v___y_4200_, v___y_4197_, v___y_4199_, v___y_4201_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_dec_ref_known(v___x_4211_, 1);
v___y_4165_ = v___y_4207_;
v___y_4166_ = v___y_4208_;
v___y_4167_ = v___y_4203_;
v___y_4168_ = v___y_4210_;
v___y_4169_ = v___y_4205_;
v___y_4170_ = v___y_4198_;
v___y_4171_ = v___y_4202_;
v___y_4172_ = v___y_4206_;
v___y_4173_ = v___y_4209_;
v___y_4174_ = v___y_4204_;
v___y_4175_ = v___y_4200_;
v___y_4176_ = v___y_4197_;
v___y_4177_ = v___y_4199_;
v___y_4178_ = v___y_4201_;
goto v___jp_4164_;
}
else
{
lean_dec_ref(v___y_4208_);
lean_dec_ref(v___y_4207_);
return v___x_4211_;
}
}
v___jp_4212_:
{
lean_object* v_size_4230_; uint8_t v___x_4231_; 
v_size_4230_ = lean_ctor_get(v___y_4223_, 6);
v___x_4231_ = lean_nat_dec_lt(v_size_4225_, v_size_4230_);
lean_dec(v_size_4225_);
if (v___x_4231_ == 0)
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
goto v___jp_4196_;
}
else
{
if (v_interpreted_4226_ == 0)
{
if (v_ctor_4227_ == 0)
{
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4215_;
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4217_;
v___y_4186_ = v___y_4218_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4220_;
v___y_4189_ = v___y_4221_;
v___y_4190_ = v___y_4222_;
v___y_4191_ = v___y_4223_;
v___y_4192_ = v___y_4224_;
v___y_4193_ = v___y_4228_;
v___y_4194_ = v___y_4229_;
goto v___jp_4180_;
}
else
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
goto v___jp_4196_;
}
}
else
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4229_;
goto v___jp_4196_;
}
}
}
v___jp_4232_:
{
if (v_ctor_4244_ == 0)
{
lean_object* v_size_4248_; uint8_t v_interpreted_4249_; uint8_t v_ctor_4250_; 
v_size_4248_ = lean_ctor_get(v___y_4245_, 6);
lean_inc(v_size_4248_);
v_interpreted_4249_ = lean_ctor_get_uint8(v___y_4245_, sizeof(void*)*12 + 1);
v_ctor_4250_ = lean_ctor_get_uint8(v___y_4245_, sizeof(void*)*12 + 2);
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4245_;
v_size_4225_ = v_size_4248_;
v_interpreted_4226_ = v_interpreted_4249_;
v_ctor_4227_ = v_ctor_4250_;
v___y_4228_ = v___y_4246_;
v___y_4229_ = v___y_4247_;
goto v___jp_4212_;
}
else
{
uint8_t v_ctor_4251_; 
v_ctor_4251_ = lean_ctor_get_uint8(v___y_4245_, sizeof(void*)*12 + 2);
if (v_ctor_4251_ == 0)
{
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
v___y_4192_ = v___y_4245_;
v___y_4193_ = v___y_4246_;
v___y_4194_ = v___y_4247_;
goto v___jp_4180_;
}
else
{
lean_object* v_size_4252_; uint8_t v_interpreted_4253_; 
v_size_4252_ = lean_ctor_get(v___y_4245_, 6);
lean_inc(v_size_4252_);
v_interpreted_4253_ = lean_ctor_get_uint8(v___y_4245_, sizeof(void*)*12 + 1);
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4245_;
v_size_4225_ = v_size_4252_;
v_interpreted_4226_ = v_interpreted_4253_;
v_ctor_4227_ = v_ctor_4251_;
v___y_4228_ = v___y_4246_;
v___y_4229_ = v___y_4247_;
goto v___jp_4212_;
}
}
}
v___jp_4254_:
{
uint8_t v_interpreted_4269_; 
v_interpreted_4269_ = lean_ctor_get_uint8(v___y_4255_, sizeof(void*)*12 + 1);
if (v_interpreted_4269_ == 0)
{
uint8_t v_ctor_4270_; 
v_ctor_4270_ = lean_ctor_get_uint8(v___y_4255_, sizeof(void*)*12 + 2);
v___y_4233_ = v___y_4266_;
v___y_4234_ = v___y_4260_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4265_;
v___y_4237_ = v___y_4268_;
v___y_4238_ = v___y_4261_;
v___y_4239_ = v_valueInconsistency_4257_;
v___y_4240_ = v___y_4264_;
v___y_4241_ = v___y_4259_;
v___y_4242_ = v___y_4262_;
v___y_4243_ = v___y_4255_;
v_ctor_4244_ = v_ctor_4270_;
v___y_4245_ = v___y_4256_;
v___y_4246_ = v___y_4263_;
v___y_4247_ = v_trueEqFalse_4258_;
goto v___jp_4232_;
}
else
{
uint8_t v_interpreted_4271_; 
v_interpreted_4271_ = lean_ctor_get_uint8(v___y_4256_, sizeof(void*)*12 + 1);
if (v_interpreted_4271_ == 0)
{
v___y_4181_ = v___y_4266_;
v___y_4182_ = v___y_4260_;
v___y_4183_ = v___y_4267_;
v___y_4184_ = v___y_4265_;
v___y_4185_ = v___y_4268_;
v___y_4186_ = v___y_4261_;
v___y_4187_ = v_valueInconsistency_4257_;
v___y_4188_ = v___y_4264_;
v___y_4189_ = v___y_4259_;
v___y_4190_ = v___y_4262_;
v___y_4191_ = v___y_4255_;
v___y_4192_ = v___y_4256_;
v___y_4193_ = v___y_4263_;
v___y_4194_ = v_trueEqFalse_4258_;
goto v___jp_4180_;
}
else
{
uint8_t v_ctor_4272_; 
v_ctor_4272_ = lean_ctor_get_uint8(v___y_4255_, sizeof(void*)*12 + 2);
v___y_4233_ = v___y_4266_;
v___y_4234_ = v___y_4260_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4265_;
v___y_4237_ = v___y_4268_;
v___y_4238_ = v___y_4261_;
v___y_4239_ = v_valueInconsistency_4257_;
v___y_4240_ = v___y_4264_;
v___y_4241_ = v___y_4259_;
v___y_4242_ = v___y_4262_;
v___y_4243_ = v___y_4255_;
v_ctor_4244_ = v_ctor_4272_;
v___y_4245_ = v___y_4256_;
v___y_4246_ = v___y_4263_;
v___y_4247_ = v_trueEqFalse_4258_;
goto v___jp_4232_;
}
}
}
v___jp_4273_:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4280_, v___y_4275_, v___y_4283_, v___y_4285_, v___y_4274_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_dec_ref_known(v___x_4286_, 1);
v___y_4255_ = v___y_4282_;
v___y_4256_ = v___y_4284_;
v_valueInconsistency_4257_ = v___x_4064_;
v_trueEqFalse_4258_ = v___x_4069_;
v___y_4259_ = v___y_4280_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4276_;
v___y_4262_ = v___y_4281_;
v___y_4263_ = v___y_4277_;
v___y_4264_ = v___y_4278_;
v___y_4265_ = v___y_4275_;
v___y_4266_ = v___y_4283_;
v___y_4267_ = v___y_4285_;
v___y_4268_ = v___y_4274_;
goto v___jp_4254_;
}
else
{
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4282_);
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
return v___x_4286_;
}
}
v___jp_4287_:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Meta_Grind_hasSameType(v___y_4301_, v___y_4295_, v___y_4289_, v___y_4299_, v___y_4300_, v___y_4288_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; uint8_t v___x_4304_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = lean_unbox(v_a_4303_);
lean_dec(v_a_4303_);
if (v___x_4304_ == 0)
{
v___y_4255_ = v___y_4297_;
v___y_4256_ = v___y_4298_;
v_valueInconsistency_4257_ = v___x_4064_;
v_trueEqFalse_4258_ = v___x_4064_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4293_;
v___y_4261_ = v___y_4290_;
v___y_4262_ = v___y_4296_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
v___y_4265_ = v___y_4289_;
v___y_4266_ = v___y_4299_;
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4288_;
goto v___jp_4254_;
}
else
{
v___y_4255_ = v___y_4297_;
v___y_4256_ = v___y_4298_;
v_valueInconsistency_4257_ = v___x_4069_;
v_trueEqFalse_4258_ = v___x_4064_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4293_;
v___y_4261_ = v___y_4290_;
v___y_4262_ = v___y_4296_;
v___y_4263_ = v___y_4291_;
v___y_4264_ = v___y_4292_;
v___y_4265_ = v___y_4289_;
v___y_4266_ = v___y_4299_;
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4288_;
goto v___jp_4254_;
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4305_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4302_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4302_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
v___jp_4313_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = lean_st_ref_get(v___y_4314_);
lean_inc_ref(v_root_4060_);
v___x_4325_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4324_, v_root_4060_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___x_4324_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4326_);
lean_dec_ref_known(v___x_4325_, 1);
v___x_4327_ = lean_st_ref_get(v___y_4314_);
lean_inc_ref(v_root_4061_);
v___x_4328_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4327_, v_root_4061_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___x_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
uint8_t v_interpreted_4329_; 
v_interpreted_4329_ = lean_ctor_get_uint8(v_a_4326_, sizeof(void*)*12 + 1);
if (v_interpreted_4329_ == 0)
{
lean_object* v_a_4330_; uint8_t v_ctor_4331_; 
v_a_4330_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4328_, 1);
v_ctor_4331_ = lean_ctor_get_uint8(v_a_4326_, sizeof(void*)*12 + 2);
v___y_4233_ = v___y_4321_;
v___y_4234_ = v___y_4315_;
v___y_4235_ = v___y_4322_;
v___y_4236_ = v___y_4320_;
v___y_4237_ = v___y_4323_;
v___y_4238_ = v___y_4316_;
v___y_4239_ = v___x_4064_;
v___y_4240_ = v___y_4319_;
v___y_4241_ = v___y_4314_;
v___y_4242_ = v___y_4317_;
v___y_4243_ = v_a_4326_;
v_ctor_4244_ = v_ctor_4331_;
v___y_4245_ = v_a_4330_;
v___y_4246_ = v___y_4318_;
v___y_4247_ = v___x_4064_;
goto v___jp_4232_;
}
else
{
lean_object* v_a_4332_; uint8_t v_interpreted_4333_; 
v_a_4332_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4328_, 1);
v_interpreted_4333_ = lean_ctor_get_uint8(v_a_4332_, sizeof(void*)*12 + 1);
if (v_interpreted_4333_ == 0)
{
v___y_4181_ = v___y_4321_;
v___y_4182_ = v___y_4315_;
v___y_4183_ = v___y_4322_;
v___y_4184_ = v___y_4320_;
v___y_4185_ = v___y_4323_;
v___y_4186_ = v___y_4316_;
v___y_4187_ = v___x_4064_;
v___y_4188_ = v___y_4319_;
v___y_4189_ = v___y_4314_;
v___y_4190_ = v___y_4317_;
v___y_4191_ = v_a_4326_;
v___y_4192_ = v_a_4332_;
v___y_4193_ = v___y_4318_;
v___y_4194_ = v___x_4064_;
goto v___jp_4180_;
}
else
{
lean_object* v_self_4334_; uint8_t v_ctor_4335_; uint8_t v_heqProofs_4336_; lean_object* v_self_4337_; uint8_t v_heqProofs_4338_; uint8_t v___x_4339_; 
v_self_4334_ = lean_ctor_get(v_a_4326_, 0);
v_ctor_4335_ = lean_ctor_get_uint8(v_a_4326_, sizeof(void*)*12 + 2);
v_heqProofs_4336_ = lean_ctor_get_uint8(v_a_4326_, sizeof(void*)*12 + 4);
v_self_4337_ = lean_ctor_get(v_a_4332_, 0);
v_heqProofs_4338_ = lean_ctor_get_uint8(v_a_4332_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4060_);
v___x_4339_ = l_Lean_Expr_isTrue(v_root_4060_);
if (v___x_4339_ == 0)
{
uint8_t v___x_4340_; 
lean_inc_ref(v_root_4061_);
v___x_4340_ = l_Lean_Expr_isTrue(v_root_4061_);
if (v___x_4340_ == 0)
{
if (v_isHEq_4039_ == 0)
{
if (v_heqProofs_4336_ == 0)
{
if (v_heqProofs_4338_ == 0)
{
v___y_4233_ = v___y_4321_;
v___y_4234_ = v___y_4315_;
v___y_4235_ = v___y_4322_;
v___y_4236_ = v___y_4320_;
v___y_4237_ = v___y_4323_;
v___y_4238_ = v___y_4316_;
v___y_4239_ = v___x_4069_;
v___y_4240_ = v___y_4319_;
v___y_4241_ = v___y_4314_;
v___y_4242_ = v___y_4317_;
v___y_4243_ = v_a_4326_;
v_ctor_4244_ = v_ctor_4335_;
v___y_4245_ = v_a_4332_;
v___y_4246_ = v___y_4318_;
v___y_4247_ = v___x_4064_;
goto v___jp_4232_;
}
else
{
lean_inc_ref(v_self_4337_);
lean_inc_ref(v_self_4334_);
v___y_4288_ = v___y_4323_;
v___y_4289_ = v___y_4320_;
v___y_4290_ = v___y_4316_;
v___y_4291_ = v___y_4318_;
v___y_4292_ = v___y_4319_;
v___y_4293_ = v___y_4315_;
v___y_4294_ = v___y_4314_;
v___y_4295_ = v_self_4337_;
v___y_4296_ = v___y_4317_;
v___y_4297_ = v_a_4326_;
v___y_4298_ = v_a_4332_;
v___y_4299_ = v___y_4321_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v_self_4334_;
goto v___jp_4287_;
}
}
else
{
lean_inc_ref(v_self_4337_);
lean_inc_ref(v_self_4334_);
v___y_4288_ = v___y_4323_;
v___y_4289_ = v___y_4320_;
v___y_4290_ = v___y_4316_;
v___y_4291_ = v___y_4318_;
v___y_4292_ = v___y_4319_;
v___y_4293_ = v___y_4315_;
v___y_4294_ = v___y_4314_;
v___y_4295_ = v_self_4337_;
v___y_4296_ = v___y_4317_;
v___y_4297_ = v_a_4326_;
v___y_4298_ = v_a_4332_;
v___y_4299_ = v___y_4321_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v_self_4334_;
goto v___jp_4287_;
}
}
else
{
lean_inc_ref(v_self_4337_);
lean_inc_ref(v_self_4334_);
v___y_4288_ = v___y_4323_;
v___y_4289_ = v___y_4320_;
v___y_4290_ = v___y_4316_;
v___y_4291_ = v___y_4318_;
v___y_4292_ = v___y_4319_;
v___y_4293_ = v___y_4315_;
v___y_4294_ = v___y_4314_;
v___y_4295_ = v_self_4337_;
v___y_4296_ = v___y_4317_;
v___y_4297_ = v_a_4326_;
v___y_4298_ = v_a_4332_;
v___y_4299_ = v___y_4321_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v_self_4334_;
goto v___jp_4287_;
}
}
else
{
v___y_4274_ = v___y_4323_;
v___y_4275_ = v___y_4320_;
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4318_;
v___y_4278_ = v___y_4319_;
v___y_4279_ = v___y_4315_;
v___y_4280_ = v___y_4314_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v_a_4326_;
v___y_4283_ = v___y_4321_;
v___y_4284_ = v_a_4332_;
v___y_4285_ = v___y_4322_;
goto v___jp_4273_;
}
}
else
{
v___y_4274_ = v___y_4323_;
v___y_4275_ = v___y_4320_;
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4318_;
v___y_4278_ = v___y_4319_;
v___y_4279_ = v___y_4315_;
v___y_4280_ = v___y_4314_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v_a_4326_;
v___y_4283_ = v___y_4321_;
v___y_4284_ = v_a_4332_;
v___y_4285_ = v___y_4322_;
goto v___jp_4273_;
}
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec(v_a_4326_);
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4341_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4328_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4328_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4349_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4325_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4325_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
else
{
lean_object* v_toCold_4395_; lean_object* v_options_4396_; uint8_t v_hasTrace_4397_; 
lean_dec(v_a_4059_);
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
v_toCold_4395_ = lean_ctor_get(v_a_4048_, 0);
v_options_4396_ = lean_ctor_get(v_toCold_4395_, 2);
v_hasTrace_4397_ = lean_ctor_get_uint8(v_options_4396_, sizeof(void*)*1);
if (v_hasTrace_4397_ == 0)
{
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
goto v___jp_4051_;
}
else
{
lean_object* v_inheritedTraceOptions_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; 
v_inheritedTraceOptions_4398_ = lean_ctor_get(v_toCold_4395_, 11);
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4398_, v_options_4396_, v___x_4400_);
if (v___x_4401_ == 0)
{
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
goto v___jp_4051_;
}
else
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_Meta_Grind_updateLastTag(v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v___x_4403_; 
lean_dec_ref_known(v___x_4402_, 1);
v___x_4403_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4036_, v_a_4040_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4037_, v_a_4040_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v___x_4407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_a_4404_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v_a_4406_);
v___x_4410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4399_, v___x_4411_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_dec_ref_known(v___x_4412_, 1);
goto v___jp_4051_;
}
else
{
return v___x_4412_;
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_a_4404_);
v_a_4413_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4405_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4405_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec_ref(v_rhs_4037_);
v_a_4421_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4403_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4403_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
return v___x_4402_;
}
}
}
}
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4056_);
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4429_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4058_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4058_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec_ref(v_proof_4038_);
lean_dec_ref(v_rhs_4037_);
lean_dec_ref(v_lhs_4036_);
v_a_4437_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4055_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4055_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
v___jp_4051_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(0);
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4445_, lean_object* v_rhs_4446_, lean_object* v_proof_4447_, lean_object* v_isHEq_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
uint8_t v_isHEq_boxed_4460_; lean_object* v_res_4461_; 
v_isHEq_boxed_4460_ = lean_unbox(v_isHEq_4448_);
v_res_4461_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4445_, v_rhs_4446_, v_proof_4447_, v_isHEq_boxed_4460_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec(v_a_4449_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4464_){
_start:
{
lean_object* v___x_4466_; lean_object* v_toGoalState_4467_; lean_object* v_mvarId_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4505_; 
v___x_4466_ = lean_st_ref_take(v_a_4464_);
v_toGoalState_4467_ = lean_ctor_get(v___x_4466_, 0);
v_mvarId_4468_ = lean_ctor_get(v___x_4466_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4470_ = v___x_4466_;
v_isShared_4471_ = v_isSharedCheck_4505_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_mvarId_4468_);
lean_inc(v_toGoalState_4467_);
lean_dec(v___x_4466_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4505_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v_nextDeclIdx_4472_; lean_object* v_enodeMap_4473_; lean_object* v_exprs_4474_; lean_object* v_parents_4475_; lean_object* v_congrTable_4476_; lean_object* v_appMap_4477_; lean_object* v_indicesFound_4478_; lean_object* v_internalizing_4479_; uint8_t v_inconsistent_4480_; lean_object* v_nextIdx_4481_; lean_object* v_newRawFacts_4482_; lean_object* v_facts_4483_; lean_object* v_extThms_4484_; lean_object* v_ematch_4485_; lean_object* v_inj_4486_; lean_object* v_split_4487_; lean_object* v_clean_4488_; lean_object* v_sstates_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4503_; 
v_nextDeclIdx_4472_ = lean_ctor_get(v_toGoalState_4467_, 0);
v_enodeMap_4473_ = lean_ctor_get(v_toGoalState_4467_, 1);
v_exprs_4474_ = lean_ctor_get(v_toGoalState_4467_, 2);
v_parents_4475_ = lean_ctor_get(v_toGoalState_4467_, 3);
v_congrTable_4476_ = lean_ctor_get(v_toGoalState_4467_, 4);
v_appMap_4477_ = lean_ctor_get(v_toGoalState_4467_, 5);
v_indicesFound_4478_ = lean_ctor_get(v_toGoalState_4467_, 6);
v_internalizing_4479_ = lean_ctor_get(v_toGoalState_4467_, 8);
v_inconsistent_4480_ = lean_ctor_get_uint8(v_toGoalState_4467_, sizeof(void*)*18);
v_nextIdx_4481_ = lean_ctor_get(v_toGoalState_4467_, 9);
v_newRawFacts_4482_ = lean_ctor_get(v_toGoalState_4467_, 10);
v_facts_4483_ = lean_ctor_get(v_toGoalState_4467_, 11);
v_extThms_4484_ = lean_ctor_get(v_toGoalState_4467_, 12);
v_ematch_4485_ = lean_ctor_get(v_toGoalState_4467_, 13);
v_inj_4486_ = lean_ctor_get(v_toGoalState_4467_, 14);
v_split_4487_ = lean_ctor_get(v_toGoalState_4467_, 15);
v_clean_4488_ = lean_ctor_get(v_toGoalState_4467_, 16);
v_sstates_4489_ = lean_ctor_get(v_toGoalState_4467_, 17);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_toGoalState_4467_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v_toGoalState_4467_, 7);
lean_dec(v_unused_4504_);
v___x_4491_ = v_toGoalState_4467_;
v_isShared_4492_ = v_isSharedCheck_4503_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_sstates_4489_);
lean_inc(v_clean_4488_);
lean_inc(v_split_4487_);
lean_inc(v_inj_4486_);
lean_inc(v_ematch_4485_);
lean_inc(v_extThms_4484_);
lean_inc(v_facts_4483_);
lean_inc(v_newRawFacts_4482_);
lean_inc(v_nextIdx_4481_);
lean_inc(v_internalizing_4479_);
lean_inc(v_indicesFound_4478_);
lean_inc(v_appMap_4477_);
lean_inc(v_congrTable_4476_);
lean_inc(v_parents_4475_);
lean_inc(v_exprs_4474_);
lean_inc(v_enodeMap_4473_);
lean_inc(v_nextDeclIdx_4472_);
lean_dec(v_toGoalState_4467_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4503_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4496_; 
v___x_4493_ = lean_box(0);
v___x_4494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 7, v___x_4494_);
v___x_4496_ = v___x_4491_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_nextDeclIdx_4472_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_enodeMap_4473_);
lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_exprs_4474_);
lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_parents_4475_);
lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_congrTable_4476_);
lean_ctor_set(v_reuseFailAlloc_4502_, 5, v_appMap_4477_);
lean_ctor_set(v_reuseFailAlloc_4502_, 6, v_indicesFound_4478_);
lean_ctor_set(v_reuseFailAlloc_4502_, 7, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4502_, 8, v_internalizing_4479_);
lean_ctor_set(v_reuseFailAlloc_4502_, 9, v_nextIdx_4481_);
lean_ctor_set(v_reuseFailAlloc_4502_, 10, v_newRawFacts_4482_);
lean_ctor_set(v_reuseFailAlloc_4502_, 11, v_facts_4483_);
lean_ctor_set(v_reuseFailAlloc_4502_, 12, v_extThms_4484_);
lean_ctor_set(v_reuseFailAlloc_4502_, 13, v_ematch_4485_);
lean_ctor_set(v_reuseFailAlloc_4502_, 14, v_inj_4486_);
lean_ctor_set(v_reuseFailAlloc_4502_, 15, v_split_4487_);
lean_ctor_set(v_reuseFailAlloc_4502_, 16, v_clean_4488_);
lean_ctor_set(v_reuseFailAlloc_4502_, 17, v_sstates_4489_);
lean_ctor_set_uint8(v_reuseFailAlloc_4502_, sizeof(void*)*18, v_inconsistent_4480_);
v___x_4496_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4498_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 0, v___x_4496_);
v___x_4498_ = v___x_4470_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4501_, 1, v_mvarId_4468_);
v___x_4498_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = lean_st_ref_put(v_a_4464_, v___x_4498_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4493_);
return v___x_4500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4506_);
lean_dec(v_a_4506_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4509_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec(v_a_4521_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v_toGoalState_4536_; lean_object* v_toProcess_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4535_ = lean_st_ref_get(v_a_4533_);
v_toGoalState_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc_ref(v_toGoalState_4536_);
lean_dec(v___x_4535_);
v_toProcess_4537_ = lean_ctor_get(v_toGoalState_4536_, 7);
lean_inc_ref(v_toProcess_4537_);
lean_dec_ref(v_toGoalState_4536_);
v___x_4538_ = lean_array_get_size(v_toProcess_4537_);
v___x_4539_ = lean_unsigned_to_nat(1u);
v___x_4540_ = lean_nat_sub(v___x_4538_, v___x_4539_);
v___x_4541_ = lean_nat_dec_lt(v___x_4540_, v___x_4538_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec(v___x_4540_);
lean_dec_ref(v_toProcess_4537_);
v___x_4542_ = lean_box(0);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
else
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v_toGoalState_4547_; lean_object* v_mvarId_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4584_; 
v___x_4544_ = lean_array_fget(v_toProcess_4537_, v___x_4540_);
lean_dec(v___x_4540_);
lean_dec_ref(v_toProcess_4537_);
v___x_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
v___x_4546_ = lean_st_ref_take(v_a_4533_);
v_toGoalState_4547_ = lean_ctor_get(v___x_4546_, 0);
v_mvarId_4548_ = lean_ctor_get(v___x_4546_, 1);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4550_ = v___x_4546_;
v_isShared_4551_ = v_isSharedCheck_4584_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_mvarId_4548_);
lean_inc(v_toGoalState_4547_);
lean_dec(v___x_4546_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4584_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v_nextDeclIdx_4552_; lean_object* v_enodeMap_4553_; lean_object* v_exprs_4554_; lean_object* v_parents_4555_; lean_object* v_congrTable_4556_; lean_object* v_appMap_4557_; lean_object* v_indicesFound_4558_; lean_object* v_toProcess_4559_; lean_object* v_internalizing_4560_; uint8_t v_inconsistent_4561_; lean_object* v_nextIdx_4562_; lean_object* v_newRawFacts_4563_; lean_object* v_facts_4564_; lean_object* v_extThms_4565_; lean_object* v_ematch_4566_; lean_object* v_inj_4567_; lean_object* v_split_4568_; lean_object* v_clean_4569_; lean_object* v_sstates_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4583_; 
v_nextDeclIdx_4552_ = lean_ctor_get(v_toGoalState_4547_, 0);
v_enodeMap_4553_ = lean_ctor_get(v_toGoalState_4547_, 1);
v_exprs_4554_ = lean_ctor_get(v_toGoalState_4547_, 2);
v_parents_4555_ = lean_ctor_get(v_toGoalState_4547_, 3);
v_congrTable_4556_ = lean_ctor_get(v_toGoalState_4547_, 4);
v_appMap_4557_ = lean_ctor_get(v_toGoalState_4547_, 5);
v_indicesFound_4558_ = lean_ctor_get(v_toGoalState_4547_, 6);
v_toProcess_4559_ = lean_ctor_get(v_toGoalState_4547_, 7);
v_internalizing_4560_ = lean_ctor_get(v_toGoalState_4547_, 8);
v_inconsistent_4561_ = lean_ctor_get_uint8(v_toGoalState_4547_, sizeof(void*)*18);
v_nextIdx_4562_ = lean_ctor_get(v_toGoalState_4547_, 9);
v_newRawFacts_4563_ = lean_ctor_get(v_toGoalState_4547_, 10);
v_facts_4564_ = lean_ctor_get(v_toGoalState_4547_, 11);
v_extThms_4565_ = lean_ctor_get(v_toGoalState_4547_, 12);
v_ematch_4566_ = lean_ctor_get(v_toGoalState_4547_, 13);
v_inj_4567_ = lean_ctor_get(v_toGoalState_4547_, 14);
v_split_4568_ = lean_ctor_get(v_toGoalState_4547_, 15);
v_clean_4569_ = lean_ctor_get(v_toGoalState_4547_, 16);
v_sstates_4570_ = lean_ctor_get(v_toGoalState_4547_, 17);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_toGoalState_4547_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4572_ = v_toGoalState_4547_;
v_isShared_4573_ = v_isSharedCheck_4583_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_sstates_4570_);
lean_inc(v_clean_4569_);
lean_inc(v_split_4568_);
lean_inc(v_inj_4567_);
lean_inc(v_ematch_4566_);
lean_inc(v_extThms_4565_);
lean_inc(v_facts_4564_);
lean_inc(v_newRawFacts_4563_);
lean_inc(v_nextIdx_4562_);
lean_inc(v_internalizing_4560_);
lean_inc(v_toProcess_4559_);
lean_inc(v_indicesFound_4558_);
lean_inc(v_appMap_4557_);
lean_inc(v_congrTable_4556_);
lean_inc(v_parents_4555_);
lean_inc(v_exprs_4554_);
lean_inc(v_enodeMap_4553_);
lean_inc(v_nextDeclIdx_4552_);
lean_dec(v_toGoalState_4547_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4583_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4574_ = lean_array_pop(v_toProcess_4559_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 7, v___x_4574_);
v___x_4576_ = v___x_4572_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_nextDeclIdx_4552_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_enodeMap_4553_);
lean_ctor_set(v_reuseFailAlloc_4582_, 2, v_exprs_4554_);
lean_ctor_set(v_reuseFailAlloc_4582_, 3, v_parents_4555_);
lean_ctor_set(v_reuseFailAlloc_4582_, 4, v_congrTable_4556_);
lean_ctor_set(v_reuseFailAlloc_4582_, 5, v_appMap_4557_);
lean_ctor_set(v_reuseFailAlloc_4582_, 6, v_indicesFound_4558_);
lean_ctor_set(v_reuseFailAlloc_4582_, 7, v___x_4574_);
lean_ctor_set(v_reuseFailAlloc_4582_, 8, v_internalizing_4560_);
lean_ctor_set(v_reuseFailAlloc_4582_, 9, v_nextIdx_4562_);
lean_ctor_set(v_reuseFailAlloc_4582_, 10, v_newRawFacts_4563_);
lean_ctor_set(v_reuseFailAlloc_4582_, 11, v_facts_4564_);
lean_ctor_set(v_reuseFailAlloc_4582_, 12, v_extThms_4565_);
lean_ctor_set(v_reuseFailAlloc_4582_, 13, v_ematch_4566_);
lean_ctor_set(v_reuseFailAlloc_4582_, 14, v_inj_4567_);
lean_ctor_set(v_reuseFailAlloc_4582_, 15, v_split_4568_);
lean_ctor_set(v_reuseFailAlloc_4582_, 16, v_clean_4569_);
lean_ctor_set(v_reuseFailAlloc_4582_, 17, v_sstates_4570_);
lean_ctor_set_uint8(v_reuseFailAlloc_4582_, sizeof(void*)*18, v_inconsistent_4561_);
v___x_4576_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
lean_object* v___x_4578_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4576_);
v___x_4578_ = v___x_4550_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_mvarId_4548_);
v___x_4578_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_st_ref_put(v_a_4533_, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4545_);
return v___x_4580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4585_);
lean_dec(v_a_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4588_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec(v_a_4600_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4612_, lean_object* v_rhs_4613_, lean_object* v_proof_4614_, uint8_t v_isHEq_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v___x_4627_; 
v___x_4627_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4612_, v_rhs_4613_, v_proof_4614_, v_isHEq_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v___x_4628_; 
lean_dec_ref_known(v___x_4627_, 1);
lean_inc(v_a_4625_);
lean_inc_ref(v_a_4624_);
lean_inc(v_a_4623_);
lean_inc_ref(v_a_4622_);
lean_inc(v_a_4621_);
lean_inc_ref(v_a_4620_);
lean_inc(v_a_4619_);
lean_inc_ref(v_a_4618_);
lean_inc(v_a_4617_);
lean_inc(v_a_4616_);
v___x_4628_ = lean_grind_process_to_do(v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
return v___x_4628_;
}
else
{
return v___x_4627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4629_, lean_object* v_rhs_4630_, lean_object* v_proof_4631_, lean_object* v_isHEq_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
uint8_t v_isHEq_boxed_4644_; lean_object* v_res_4645_; 
v_isHEq_boxed_4644_ = lean_unbox(v_isHEq_4632_);
v_res_4645_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4629_, v_rhs_4630_, v_proof_4631_, v_isHEq_boxed_4644_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
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
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4646_, lean_object* v_rhs_4647_, lean_object* v_proof_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
uint8_t v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = 0;
v___x_4661_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4646_, v_rhs_4647_, v_proof_4648_, v___x_4660_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4662_, lean_object* v_rhs_4663_, lean_object* v_proof_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4662_, v_rhs_4663_, v_proof_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec(v_a_4665_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4677_, lean_object* v_rhs_4678_, lean_object* v_proof_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_){
_start:
{
uint8_t v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = 1;
v___x_4692_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4677_, v_rhs_4678_, v_proof_4679_, v___x_4691_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4693_, lean_object* v_rhs_4694_, lean_object* v_proof_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4693_, v_rhs_4694_, v_proof_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
lean_dec(v_a_4705_);
lean_dec_ref(v_a_4704_);
lean_dec(v_a_4703_);
lean_dec_ref(v_a_4702_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec(v_a_4696_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v___x_4711_; lean_object* v_toGoalState_4712_; lean_object* v_mvarId_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4750_; 
v___x_4711_ = lean_st_ref_take(v_a_4709_);
v_toGoalState_4712_ = lean_ctor_get(v___x_4711_, 0);
v_mvarId_4713_ = lean_ctor_get(v___x_4711_, 1);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4715_ = v___x_4711_;
v_isShared_4716_ = v_isSharedCheck_4750_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_mvarId_4713_);
lean_inc(v_toGoalState_4712_);
lean_dec(v___x_4711_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4750_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v_nextDeclIdx_4717_; lean_object* v_enodeMap_4718_; lean_object* v_exprs_4719_; lean_object* v_parents_4720_; lean_object* v_congrTable_4721_; lean_object* v_appMap_4722_; lean_object* v_indicesFound_4723_; lean_object* v_toProcess_4724_; lean_object* v_internalizing_4725_; uint8_t v_inconsistent_4726_; lean_object* v_nextIdx_4727_; lean_object* v_newRawFacts_4728_; lean_object* v_facts_4729_; lean_object* v_extThms_4730_; lean_object* v_ematch_4731_; lean_object* v_inj_4732_; lean_object* v_split_4733_; lean_object* v_clean_4734_; lean_object* v_sstates_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4749_; 
v_nextDeclIdx_4717_ = lean_ctor_get(v_toGoalState_4712_, 0);
v_enodeMap_4718_ = lean_ctor_get(v_toGoalState_4712_, 1);
v_exprs_4719_ = lean_ctor_get(v_toGoalState_4712_, 2);
v_parents_4720_ = lean_ctor_get(v_toGoalState_4712_, 3);
v_congrTable_4721_ = lean_ctor_get(v_toGoalState_4712_, 4);
v_appMap_4722_ = lean_ctor_get(v_toGoalState_4712_, 5);
v_indicesFound_4723_ = lean_ctor_get(v_toGoalState_4712_, 6);
v_toProcess_4724_ = lean_ctor_get(v_toGoalState_4712_, 7);
v_internalizing_4725_ = lean_ctor_get(v_toGoalState_4712_, 8);
v_inconsistent_4726_ = lean_ctor_get_uint8(v_toGoalState_4712_, sizeof(void*)*18);
v_nextIdx_4727_ = lean_ctor_get(v_toGoalState_4712_, 9);
v_newRawFacts_4728_ = lean_ctor_get(v_toGoalState_4712_, 10);
v_facts_4729_ = lean_ctor_get(v_toGoalState_4712_, 11);
v_extThms_4730_ = lean_ctor_get(v_toGoalState_4712_, 12);
v_ematch_4731_ = lean_ctor_get(v_toGoalState_4712_, 13);
v_inj_4732_ = lean_ctor_get(v_toGoalState_4712_, 14);
v_split_4733_ = lean_ctor_get(v_toGoalState_4712_, 15);
v_clean_4734_ = lean_ctor_get(v_toGoalState_4712_, 16);
v_sstates_4735_ = lean_ctor_get(v_toGoalState_4712_, 17);
v_isSharedCheck_4749_ = !lean_is_exclusive(v_toGoalState_4712_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4737_ = v_toGoalState_4712_;
v_isShared_4738_ = v_isSharedCheck_4749_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_sstates_4735_);
lean_inc(v_clean_4734_);
lean_inc(v_split_4733_);
lean_inc(v_inj_4732_);
lean_inc(v_ematch_4731_);
lean_inc(v_extThms_4730_);
lean_inc(v_facts_4729_);
lean_inc(v_newRawFacts_4728_);
lean_inc(v_nextIdx_4727_);
lean_inc(v_internalizing_4725_);
lean_inc(v_toProcess_4724_);
lean_inc(v_indicesFound_4723_);
lean_inc(v_appMap_4722_);
lean_inc(v_congrTable_4721_);
lean_inc(v_parents_4720_);
lean_inc(v_exprs_4719_);
lean_inc(v_enodeMap_4718_);
lean_inc(v_nextDeclIdx_4717_);
lean_dec(v_toGoalState_4712_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4749_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4742_; 
v___x_4739_ = lean_box(0);
v___x_4740_ = l_Lean_PersistentArray_push___redArg(v_facts_4729_, v_fact_4708_);
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 11, v___x_4740_);
v___x_4742_ = v___x_4737_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_nextDeclIdx_4717_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_enodeMap_4718_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_exprs_4719_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_parents_4720_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v_congrTable_4721_);
lean_ctor_set(v_reuseFailAlloc_4748_, 5, v_appMap_4722_);
lean_ctor_set(v_reuseFailAlloc_4748_, 6, v_indicesFound_4723_);
lean_ctor_set(v_reuseFailAlloc_4748_, 7, v_toProcess_4724_);
lean_ctor_set(v_reuseFailAlloc_4748_, 8, v_internalizing_4725_);
lean_ctor_set(v_reuseFailAlloc_4748_, 9, v_nextIdx_4727_);
lean_ctor_set(v_reuseFailAlloc_4748_, 10, v_newRawFacts_4728_);
lean_ctor_set(v_reuseFailAlloc_4748_, 11, v___x_4740_);
lean_ctor_set(v_reuseFailAlloc_4748_, 12, v_extThms_4730_);
lean_ctor_set(v_reuseFailAlloc_4748_, 13, v_ematch_4731_);
lean_ctor_set(v_reuseFailAlloc_4748_, 14, v_inj_4732_);
lean_ctor_set(v_reuseFailAlloc_4748_, 15, v_split_4733_);
lean_ctor_set(v_reuseFailAlloc_4748_, 16, v_clean_4734_);
lean_ctor_set(v_reuseFailAlloc_4748_, 17, v_sstates_4735_);
lean_ctor_set_uint8(v_reuseFailAlloc_4748_, sizeof(void*)*18, v_inconsistent_4726_);
v___x_4742_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4744_; 
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v___x_4742_);
v___x_4744_ = v___x_4715_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4742_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_mvarId_4713_);
v___x_4744_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = lean_st_ref_put(v_a_4709_, v___x_4744_);
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4739_);
return v___x_4746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4751_, v_a_4752_);
lean_dec(v_a_4752_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___x_4767_; 
v___x_4767_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4755_, v_a_4756_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec(v_a_4769_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4781_, lean_object* v_rhs_4782_, lean_object* v_proof_4783_, lean_object* v_generation_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v___x_4796_; 
lean_inc_ref(v_rhs_4782_);
lean_inc_ref(v_lhs_4781_);
v___x_4796_ = l_Lean_Meta_mkEq(v_lhs_4781_, v_rhs_4782_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4808_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc_n(v_a_4797_, 2);
lean_dec_ref_known(v___x_4796_, 1);
v___x_4798_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4797_, v_a_4785_);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v___x_4798_, 0);
lean_dec(v_unused_4809_);
v___x_4800_ = v___x_4798_;
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
else
{
lean_dec(v___x_4798_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
lean_ctor_set_tag(v___x_4800_, 1);
lean_ctor_set(v___x_4800_, 0, v_a_4797_);
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4797_);
v___x_4803_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
lean_object* v___x_4804_; 
lean_inc(v_a_4794_);
lean_inc_ref(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc_ref(v_a_4791_);
lean_inc(v_a_4790_);
lean_inc_ref(v_a_4789_);
lean_inc(v_a_4788_);
lean_inc_ref(v_a_4787_);
lean_inc(v_a_4786_);
lean_inc(v_a_4785_);
lean_inc_ref(v___x_4803_);
lean_inc(v_generation_4784_);
lean_inc_ref(v_lhs_4781_);
v___x_4804_ = lean_grind_internalize(v_lhs_4781_, v_generation_4784_, v___x_4803_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v___x_4805_; 
lean_dec_ref_known(v___x_4804_, 1);
lean_inc(v_a_4794_);
lean_inc_ref(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc_ref(v_a_4791_);
lean_inc(v_a_4790_);
lean_inc_ref(v_a_4789_);
lean_inc(v_a_4788_);
lean_inc_ref(v_a_4787_);
lean_inc(v_a_4786_);
lean_inc(v_a_4785_);
lean_inc_ref(v_rhs_4782_);
v___x_4805_ = lean_grind_internalize(v_rhs_4782_, v_generation_4784_, v___x_4803_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v___x_4806_; 
lean_dec_ref_known(v___x_4805_, 1);
v___x_4806_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4781_, v_rhs_4782_, v_proof_4783_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
return v___x_4806_;
}
else
{
lean_dec_ref(v_proof_4783_);
lean_dec_ref(v_rhs_4782_);
lean_dec_ref(v_lhs_4781_);
return v___x_4805_;
}
}
else
{
lean_dec_ref(v___x_4803_);
lean_dec(v_generation_4784_);
lean_dec_ref(v_proof_4783_);
lean_dec_ref(v_rhs_4782_);
lean_dec_ref(v_lhs_4781_);
return v___x_4804_;
}
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec(v_generation_4784_);
lean_dec_ref(v_proof_4783_);
lean_dec_ref(v_rhs_4782_);
lean_dec_ref(v_lhs_4781_);
v_a_4810_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4796_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4796_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4818_, lean_object* v_rhs_4819_, lean_object* v_proof_4820_, lean_object* v_generation_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4818_, v_rhs_4819_, v_proof_4820_, v_generation_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec(v_a_4822_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4834_, lean_object* v_generation_4835_, lean_object* v_p_4836_, uint8_t v_isNeg_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_box(0);
lean_inc(v_a_4847_);
lean_inc_ref(v_a_4846_);
lean_inc(v_a_4845_);
lean_inc_ref(v_a_4844_);
lean_inc(v_a_4843_);
lean_inc_ref(v_a_4842_);
lean_inc(v_a_4841_);
lean_inc_ref(v_a_4840_);
lean_inc(v_a_4839_);
lean_inc(v_a_4838_);
lean_inc_ref(v_p_4836_);
v___x_4850_ = lean_grind_internalize(v_p_4836_, v_generation_4835_, v___x_4849_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_dec_ref_known(v___x_4850_, 1);
if (v_isNeg_4837_ == 0)
{
lean_object* v___x_4851_; 
v___x_4851_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4842_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v___x_4853_ = l_Lean_Meta_mkEqTrue(v_proof_4834_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4855_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___x_4853_, 1);
v___x_4855_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4836_, v_a_4852_, v_a_4854_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
return v___x_4855_;
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec(v_a_4852_);
lean_dec_ref(v_p_4836_);
v_a_4856_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4853_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4853_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec_ref(v_p_4836_);
lean_dec_ref(v_proof_4834_);
v_a_4864_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4851_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4851_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
else
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4842_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
v___x_4874_ = l_Lean_Meta_mkEqFalse(v_proof_4834_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v___x_4876_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4836_, v_a_4873_, v_a_4875_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_);
return v___x_4876_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v_a_4873_);
lean_dec_ref(v_p_4836_);
v_a_4877_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4874_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4874_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec_ref(v_p_4836_);
lean_dec_ref(v_proof_4834_);
v_a_4885_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4872_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4872_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4836_);
lean_dec_ref(v_proof_4834_);
return v___x_4850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4893_, lean_object* v_generation_4894_, lean_object* v_p_4895_, lean_object* v_isNeg_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
uint8_t v_isNeg_boxed_4908_; lean_object* v_res_4909_; 
v_isNeg_boxed_4908_ = lean_unbox(v_isNeg_4896_);
v_res_4909_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4893_, v_generation_4894_, v_p_4895_, v_isNeg_boxed_4908_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec_ref(v_a_4903_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec(v_a_4897_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4910_, lean_object* v_generation_4911_, lean_object* v_p_4912_, lean_object* v_lhs_4913_, lean_object* v_rhs_4914_, uint8_t v_isNeg_4915_, uint8_t v_isHEq_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_){
_start:
{
if (v_isNeg_4915_ == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_inc_ref(v_p_4912_);
v___x_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4928_, 0, v_p_4912_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc(v_a_4917_);
lean_inc_ref(v___x_4928_);
lean_inc(v_generation_4911_);
lean_inc_ref(v_lhs_4913_);
v___x_4929_ = lean_grind_internalize(v_lhs_4913_, v_generation_4911_, v___x_4928_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v___x_4930_; 
lean_dec_ref_known(v___x_4929_, 1);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc(v_a_4917_);
lean_inc_ref(v_rhs_4914_);
v___x_4930_ = lean_grind_internalize(v_rhs_4914_, v_generation_4911_, v___x_4928_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
lean_dec_ref_known(v___x_4930_, 1);
v___x_4931_ = lean_box(0);
v___x_4932_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4912_, v___x_4931_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v___x_4933_; 
lean_dec_ref_known(v___x_4932_, 1);
v___x_4933_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4913_, v_rhs_4914_, v_proof_4910_, v_isHEq_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
return v___x_4933_;
}
else
{
lean_dec_ref(v_rhs_4914_);
lean_dec_ref(v_lhs_4913_);
lean_dec_ref(v_proof_4910_);
return v___x_4932_;
}
}
else
{
lean_dec_ref(v_rhs_4914_);
lean_dec_ref(v_lhs_4913_);
lean_dec_ref(v_p_4912_);
lean_dec_ref(v_proof_4910_);
return v___x_4930_;
}
}
else
{
lean_dec_ref_known(v___x_4928_, 1);
lean_dec_ref(v_rhs_4914_);
lean_dec_ref(v_lhs_4913_);
lean_dec_ref(v_p_4912_);
lean_dec(v_generation_4911_);
lean_dec_ref(v_proof_4910_);
return v___x_4929_;
}
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_dec_ref(v_rhs_4914_);
lean_dec_ref(v_lhs_4913_);
v___x_4934_ = lean_box(0);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_a_4923_);
lean_inc(v_a_4922_);
lean_inc_ref(v_a_4921_);
lean_inc(v_a_4920_);
lean_inc_ref(v_a_4919_);
lean_inc(v_a_4918_);
lean_inc(v_a_4917_);
lean_inc_ref(v_p_4912_);
v___x_4935_ = lean_grind_internalize(v_p_4912_, v_generation_4911_, v___x_4934_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4936_; 
lean_dec_ref_known(v___x_4935_, 1);
v___x_4936_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4921_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4938_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = l_Lean_Meta_mkEqFalse(v_proof_4910_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4940_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v___x_4940_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4912_, v_a_4937_, v_a_4939_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
return v___x_4940_;
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_a_4937_);
lean_dec_ref(v_p_4912_);
v_a_4941_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4938_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4938_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec_ref(v_p_4912_);
lean_dec_ref(v_proof_4910_);
v_a_4949_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4936_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4936_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_dec_ref(v_p_4912_);
lean_dec_ref(v_proof_4910_);
return v___x_4935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4957_ = _args[0];
lean_object* v_generation_4958_ = _args[1];
lean_object* v_p_4959_ = _args[2];
lean_object* v_lhs_4960_ = _args[3];
lean_object* v_rhs_4961_ = _args[4];
lean_object* v_isNeg_4962_ = _args[5];
lean_object* v_isHEq_4963_ = _args[6];
lean_object* v_a_4964_ = _args[7];
lean_object* v_a_4965_ = _args[8];
lean_object* v_a_4966_ = _args[9];
lean_object* v_a_4967_ = _args[10];
lean_object* v_a_4968_ = _args[11];
lean_object* v_a_4969_ = _args[12];
lean_object* v_a_4970_ = _args[13];
lean_object* v_a_4971_ = _args[14];
lean_object* v_a_4972_ = _args[15];
lean_object* v_a_4973_ = _args[16];
lean_object* v_a_4974_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4975_; uint8_t v_isHEq_boxed_4976_; lean_object* v_res_4977_; 
v_isNeg_boxed_4975_ = lean_unbox(v_isNeg_4962_);
v_isHEq_boxed_4976_ = lean_unbox(v_isHEq_4963_);
v_res_4977_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4957_, v_generation_4958_, v_p_4959_, v_lhs_4960_, v_rhs_4961_, v_isNeg_boxed_4975_, v_isHEq_boxed_4976_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec(v_a_4971_);
lean_dec_ref(v_a_4970_);
lean_dec(v_a_4969_);
lean_dec_ref(v_a_4968_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec(v_a_4964_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4981_, lean_object* v_generation_4982_, lean_object* v_p_4983_, uint8_t v_isNeg_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v___x_4996_; 
lean_inc_ref(v_p_4983_);
v___x_4996_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4983_, v_a_4992_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v_a_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref_known(v___x_4996_, 1);
v___x_4998_ = l_Lean_Expr_cleanupAnnotations(v_a_4997_);
v___x_4999_ = l_Lean_Expr_isApp(v___x_4998_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref(v___x_4998_);
v___x_5000_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5000_;
}
else
{
lean_object* v_arg_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
v_arg_5001_ = lean_ctor_get(v___x_4998_, 1);
lean_inc_ref(v_arg_5001_);
v___x_5002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4998_);
v___x_5003_ = l_Lean_Expr_isApp(v___x_5002_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
lean_dec_ref(v___x_5002_);
lean_dec_ref(v_arg_5001_);
v___x_5004_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5004_;
}
else
{
lean_object* v_arg_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v_arg_5005_ = lean_ctor_get(v___x_5002_, 1);
lean_inc_ref(v_arg_5005_);
v___x_5006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5002_);
v___x_5007_ = l_Lean_Expr_isApp(v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; 
lean_dec_ref(v___x_5006_);
lean_dec_ref(v_arg_5005_);
lean_dec_ref(v_arg_5001_);
v___x_5008_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5008_;
}
else
{
lean_object* v_arg_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v_arg_5009_ = lean_ctor_get(v___x_5006_, 1);
lean_inc_ref(v_arg_5009_);
v___x_5010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5006_);
v___x_5011_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5012_ = l_Lean_Expr_isConstOf(v___x_5010_, v___x_5011_);
if (v___x_5012_ == 0)
{
uint8_t v___x_5013_; 
lean_dec_ref(v_arg_5005_);
v___x_5013_ = l_Lean_Expr_isApp(v___x_5010_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; 
lean_dec_ref(v___x_5010_);
lean_dec_ref(v_arg_5009_);
lean_dec_ref(v_arg_5001_);
v___x_5014_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5014_;
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; 
v___x_5015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5010_);
v___x_5016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5017_ = l_Lean_Expr_isConstOf(v___x_5015_, v___x_5016_);
lean_dec_ref(v___x_5015_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; 
lean_dec_ref(v_arg_5009_);
lean_dec_ref(v_arg_5001_);
v___x_5018_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5018_;
}
else
{
lean_object* v___x_5019_; 
v___x_5019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4981_, v_generation_4982_, v_p_4983_, v_arg_5009_, v_arg_5001_, v_isNeg_4984_, v___x_5017_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5019_;
}
}
}
else
{
uint8_t v___x_5020_; 
lean_dec_ref(v___x_5010_);
v___x_5020_ = l_Lean_Expr_isProp(v_arg_5009_);
lean_dec_ref(v_arg_5009_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
v___x_5021_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4981_, v_generation_4982_, v_p_4983_, v_arg_5005_, v_arg_5001_, v_isNeg_4984_, v___x_5020_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; 
lean_dec_ref(v_arg_5005_);
lean_dec_ref(v_arg_5001_);
v___x_5022_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4981_, v_generation_4982_, v_p_4983_, v_isNeg_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
return v___x_5022_;
}
}
}
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec_ref(v_p_4983_);
lean_dec(v_generation_4982_);
lean_dec_ref(v_proof_4981_);
v_a_5023_ = lean_ctor_get(v___x_4996_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_4996_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___x_4996_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_4996_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5031_, lean_object* v_generation_5032_, lean_object* v_p_5033_, lean_object* v_isNeg_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_){
_start:
{
uint8_t v_isNeg_boxed_5046_; lean_object* v_res_5047_; 
v_isNeg_boxed_5046_ = lean_unbox(v_isNeg_5034_);
v_res_5047_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5031_, v_generation_5032_, v_p_5033_, v_isNeg_boxed_5046_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec(v_a_5035_);
return v_res_5047_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5056_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5057_ = l_Lean_Name_append(v___x_5056_, v___x_5055_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5058_, lean_object* v_proof_5059_, lean_object* v_generation_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___x_5103_; lean_object* v_toCold_5104_; lean_object* v_options_5105_; uint8_t v_hasTrace_5106_; 
lean_inc_ref(v_fact_5058_);
v___x_5103_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5058_, v_a_5061_);
lean_dec_ref(v___x_5103_);
v_toCold_5104_ = lean_ctor_get(v_a_5069_, 0);
v_options_5105_ = lean_ctor_get(v_toCold_5104_, 2);
v_hasTrace_5106_ = lean_ctor_get_uint8(v_options_5105_, sizeof(void*)*1);
if (v_hasTrace_5106_ == 0)
{
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
goto v___jp_5085_;
}
else
{
lean_object* v_inheritedTraceOptions_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v_inheritedTraceOptions_5107_ = lean_ctor_get(v_toCold_5104_, 11);
v___x_5108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5107_, v_options_5105_, v___x_5109_);
if (v___x_5110_ == 0)
{
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
goto v___jp_5085_;
}
else
{
lean_object* v___x_5111_; 
v___x_5111_ = l_Lean_Meta_Grind_updateLastTag(v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v___x_5112_; lean_object* v___x_5113_; 
lean_dec_ref_known(v___x_5111_, 1);
lean_inc_ref(v_fact_5058_);
v___x_5112_ = l_Lean_MessageData_ofExpr(v_fact_5058_);
v___x_5113_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5108_, v___x_5112_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_dec_ref_known(v___x_5113_, 1);
v___y_5086_ = v_a_5061_;
v___y_5087_ = v_a_5062_;
v___y_5088_ = v_a_5063_;
v___y_5089_ = v_a_5064_;
v___y_5090_ = v_a_5065_;
v___y_5091_ = v_a_5066_;
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
goto v___jp_5085_;
}
else
{
lean_dec(v_generation_5060_);
lean_dec_ref(v_proof_5059_);
lean_dec_ref(v_fact_5058_);
return v___x_5113_;
}
}
else
{
lean_dec(v_generation_5060_);
lean_dec_ref(v_proof_5059_);
lean_dec_ref(v_fact_5058_);
return v___x_5111_;
}
}
}
v___jp_5072_:
{
uint8_t v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = 0;
v___x_5084_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5059_, v_generation_5060_, v_fact_5058_, v___x_5083_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
return v___x_5084_;
}
v___jp_5085_:
{
lean_object* v___x_5096_; uint8_t v___x_5097_; 
lean_inc_ref(v_fact_5058_);
v___x_5096_ = l_Lean_Expr_cleanupAnnotations(v_fact_5058_);
v___x_5097_ = l_Lean_Expr_isApp(v___x_5096_);
if (v___x_5097_ == 0)
{
lean_dec_ref(v___x_5096_);
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5088_;
v___y_5076_ = v___y_5089_;
v___y_5077_ = v___y_5090_;
v___y_5078_ = v___y_5091_;
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
goto v___jp_5072_;
}
else
{
lean_object* v_arg_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; 
v_arg_5098_ = lean_ctor_get(v___x_5096_, 1);
lean_inc_ref(v_arg_5098_);
v___x_5099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5096_);
v___x_5100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5101_ = l_Lean_Expr_isConstOf(v___x_5099_, v___x_5100_);
lean_dec_ref(v___x_5099_);
if (v___x_5101_ == 0)
{
lean_dec_ref(v_arg_5098_);
v___y_5073_ = v___y_5086_;
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5088_;
v___y_5076_ = v___y_5089_;
v___y_5077_ = v___y_5090_;
v___y_5078_ = v___y_5091_;
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
goto v___jp_5072_;
}
else
{
lean_object* v___x_5102_; 
lean_dec_ref(v_fact_5058_);
v___x_5102_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5059_, v_generation_5060_, v_arg_5098_, v___x_5101_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
return v___x_5102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5114_, lean_object* v_proof_5115_, lean_object* v_generation_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5114_, v_proof_5115_, v_generation_5116_, v_a_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_);
lean_dec(v_a_5126_);
lean_dec_ref(v_a_5125_);
lean_dec(v_a_5124_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
lean_dec(v_a_5118_);
lean_dec(v_a_5117_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5132_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; uint8_t v___x_5145_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
lean_dec_ref_known(v___x_5143_, 1);
v___x_5145_ = lean_unbox(v_a_5144_);
lean_dec(v_a_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5147_ = l_Lean_Core_checkSystem(v___x_5146_, v___y_5140_, v___y_5141_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v___x_5148_; 
lean_dec_ref_known(v___x_5147_, 1);
v___x_5148_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5132_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5222_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5151_ = v___x_5148_;
v_isShared_5152_ = v_isSharedCheck_5222_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5148_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5222_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
if (lean_obj_tag(v_a_5149_) == 1)
{
lean_object* v_val_5153_; 
lean_del_object(v___x_5151_);
v_val_5153_ = lean_ctor_get(v_a_5149_, 0);
lean_inc(v_val_5153_);
lean_dec_ref_known(v_a_5149_, 1);
switch(lean_obj_tag(v_val_5153_))
{
case 0:
{
lean_object* v_lhs_5154_; lean_object* v_rhs_5155_; lean_object* v_proof_5156_; uint8_t v_isHEq_5157_; lean_object* v___x_5158_; 
v_lhs_5154_ = lean_ctor_get(v_val_5153_, 0);
lean_inc_ref(v_lhs_5154_);
v_rhs_5155_ = lean_ctor_get(v_val_5153_, 1);
lean_inc_ref(v_rhs_5155_);
v_proof_5156_ = lean_ctor_get(v_val_5153_, 2);
lean_inc_ref(v_proof_5156_);
v_isHEq_5157_ = lean_ctor_get_uint8(v_val_5153_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5153_, 3);
v___x_5158_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5154_, v_rhs_5155_, v_proof_5156_, v_isHEq_5157_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_dec_ref_known(v___x_5158_, 1);
goto _start;
}
else
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
v_a_5160_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5158_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5158_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
}
case 1:
{
lean_object* v_prop_5168_; lean_object* v_proof_5169_; lean_object* v_generation_5170_; lean_object* v___x_5171_; 
v_prop_5168_ = lean_ctor_get(v_val_5153_, 0);
lean_inc_ref(v_prop_5168_);
v_proof_5169_ = lean_ctor_get(v_val_5153_, 1);
lean_inc_ref(v_proof_5169_);
v_generation_5170_ = lean_ctor_get(v_val_5153_, 2);
lean_inc(v_generation_5170_);
lean_dec_ref_known(v_val_5153_, 3);
v___x_5171_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5168_, v_proof_5169_, v_generation_5170_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
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
case 2:
{
lean_object* v_e_5181_; lean_object* v___x_5182_; 
v_e_5181_ = lean_ctor_get(v_val_5153_, 0);
lean_inc_ref(v_e_5181_);
lean_dec_ref_known(v_val_5153_, 1);
v___x_5182_ = l_Lean_Meta_Grind_propagateUp(v_e_5181_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_dec_ref_known(v___x_5182_, 1);
goto _start;
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
v_a_5184_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5182_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5182_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
case 3:
{
lean_object* v_solverId_5192_; lean_object* v_lhs_5193_; lean_object* v_rhs_5194_; lean_object* v___x_5195_; 
v_solverId_5192_ = lean_ctor_get(v_val_5153_, 0);
lean_inc(v_solverId_5192_);
v_lhs_5193_ = lean_ctor_get(v_val_5153_, 1);
lean_inc_ref(v_lhs_5193_);
v_rhs_5194_ = lean_ctor_get(v_val_5153_, 2);
lean_inc_ref(v_rhs_5194_);
lean_dec_ref_known(v_val_5153_, 3);
v___x_5195_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5192_, v_lhs_5193_, v_rhs_5194_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v_solverId_5192_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_dec_ref_known(v___x_5195_, 1);
goto _start;
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
v_a_5197_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5195_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5195_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
default: 
{
lean_object* v_solverId_5205_; lean_object* v_lhs_5206_; lean_object* v_rhs_5207_; lean_object* v___x_5208_; 
v_solverId_5205_ = lean_ctor_get(v_val_5153_, 0);
lean_inc(v_solverId_5205_);
v_lhs_5206_ = lean_ctor_get(v_val_5153_, 1);
lean_inc_ref(v_lhs_5206_);
v_rhs_5207_ = lean_ctor_get(v_val_5153_, 2);
lean_inc_ref(v_rhs_5207_);
lean_dec_ref_known(v_val_5153_, 3);
v___x_5208_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5205_, v_lhs_5206_, v_rhs_5207_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v_solverId_5205_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_dec_ref_known(v___x_5208_, 1);
goto _start;
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
v_a_5210_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5208_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5208_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
}
}
else
{
lean_object* v___x_5218_; lean_object* v___x_5220_; 
lean_dec(v_a_5149_);
v___x_5218_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5218_);
v___x_5220_ = v___x_5151_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5218_);
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
else
{
lean_object* v_a_5223_; lean_object* v___x_5225_; uint8_t v_isShared_5226_; uint8_t v_isSharedCheck_5230_; 
v_a_5223_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5225_ = v___x_5148_;
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
else
{
lean_inc(v_a_5223_);
lean_dec(v___x_5148_);
v___x_5225_ = lean_box(0);
v_isShared_5226_ = v_isSharedCheck_5230_;
goto v_resetjp_5224_;
}
v_resetjp_5224_:
{
lean_object* v___x_5228_; 
if (v_isShared_5226_ == 0)
{
v___x_5228_ = v___x_5225_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
v_a_5231_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5147_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5147_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
}
}
else
{
lean_object* v___x_5239_; 
v___x_5239_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5132_);
if (lean_obj_tag(v___x_5239_) == 0)
{
lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5247_; 
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5239_);
if (v_isSharedCheck_5247_ == 0)
{
lean_object* v_unused_5248_; 
v_unused_5248_ = lean_ctor_get(v___x_5239_, 0);
lean_dec(v_unused_5248_);
v___x_5241_ = v___x_5239_;
v_isShared_5242_ = v_isSharedCheck_5247_;
goto v_resetjp_5240_;
}
else
{
lean_dec(v___x_5239_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5247_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5243_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5242_ == 0)
{
lean_ctor_set(v___x_5241_, 0, v___x_5243_);
v___x_5245_ = v___x_5241_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5243_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
v_a_5249_ = lean_ctor_get(v___x_5239_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5239_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5239_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5239_);
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
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_a_5257_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5143_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5143_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec(v___y_5265_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5288_ = lean_box(0);
v___x_5289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_a_5284_);
lean_dec_ref(v_a_5283_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
lean_dec(v_a_5278_);
lean_dec(v_a_5277_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5302_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5292_ = v___x_5289_;
v_isShared_5293_ = v_isSharedCheck_5302_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5289_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5302_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v_fst_5294_; 
v_fst_5294_ = lean_ctor_get(v_a_5290_, 0);
lean_inc(v_fst_5294_);
lean_dec(v_a_5290_);
if (lean_obj_tag(v_fst_5294_) == 0)
{
lean_object* v___x_5296_; 
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v___x_5288_);
v___x_5296_ = v___x_5292_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5288_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
else
{
lean_object* v_val_5298_; lean_object* v___x_5300_; 
v_val_5298_ = lean_ctor_get(v_fst_5294_, 0);
lean_inc(v_val_5298_);
lean_dec_ref_known(v_fst_5294_, 1);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v_val_5298_);
v___x_5300_ = v___x_5292_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_val_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
v_a_5303_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5289_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5289_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = lean_grind_process_to_do(v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5323_, lean_object* v_a_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v___x_5336_; 
v___x_5336_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5337_, lean_object* v_a_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5337_, v_a_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v_a_5338_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5351_, lean_object* v_proof_5352_, lean_object* v_generation_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_){
_start:
{
uint8_t v___x_5365_; 
lean_inc_ref(v_fact_5351_);
v___x_5365_ = l_Lean_Expr_isTrue(v_fact_5351_);
if (v___x_5365_ == 0)
{
lean_object* v___x_5366_; 
v___x_5366_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5354_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5397_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5369_ = v___x_5366_;
v_isShared_5370_ = v_isSharedCheck_5397_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5366_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5397_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
uint8_t v___x_5371_; 
v___x_5371_ = lean_unbox(v_a_5367_);
lean_dec(v_a_5367_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
lean_del_object(v___x_5369_);
lean_inc(v_a_5363_);
lean_inc_ref(v_a_5362_);
lean_inc(v_a_5361_);
lean_inc_ref(v_a_5360_);
lean_inc(v_a_5359_);
lean_inc_ref(v_a_5358_);
lean_inc(v_a_5357_);
lean_inc_ref(v_a_5356_);
lean_inc(v_a_5355_);
lean_inc(v_a_5354_);
v___x_5372_ = lean_grind_process_to_do(v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v___x_5373_; 
lean_dec_ref_known(v___x_5372_, 1);
v___x_5373_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5354_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5384_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5384_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5384_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
uint8_t v___x_5378_; 
v___x_5378_ = lean_unbox(v_a_5374_);
lean_dec(v_a_5374_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; 
lean_del_object(v___x_5376_);
v___x_5379_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5351_, v_proof_5352_, v_generation_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_);
return v___x_5379_;
}
else
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
v___x_5380_ = lean_box(0);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v___x_5380_);
v___x_5382_ = v___x_5376_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
v_a_5385_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5373_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5373_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
else
{
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
return v___x_5372_;
}
}
else
{
lean_object* v___x_5393_; lean_object* v___x_5395_; 
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
v___x_5393_ = lean_box(0);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v___x_5393_);
v___x_5395_ = v___x_5369_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5393_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
return v___x_5395_;
}
}
}
}
else
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
v_a_5398_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5366_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5366_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
else
{
lean_object* v___x_5406_; lean_object* v___x_5407_; 
lean_dec(v_generation_5353_);
lean_dec_ref(v_proof_5352_);
lean_dec_ref(v_fact_5351_);
v___x_5406_ = lean_box(0);
v___x_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5406_);
return v___x_5407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5408_, lean_object* v_proof_5409_, lean_object* v_generation_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_Meta_Grind_add(v_fact_5408_, v_proof_5409_, v_generation_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
lean_dec(v_a_5412_);
lean_dec(v_a_5411_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5423_, lean_object* v_generation_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v___x_5436_; 
lean_inc(v_fvarId_5423_);
v___x_5436_ = l_Lean_FVarId_getType___redArg(v_fvarId_5423_, v_a_5431_, v_a_5433_, v_a_5434_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = l_Lean_mkFVar(v_fvarId_5423_);
v___x_5439_ = l_Lean_Meta_Grind_add(v_a_5437_, v___x_5438_, v_generation_5424_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
return v___x_5439_;
}
else
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
lean_dec(v_generation_5424_);
lean_dec(v_fvarId_5423_);
v_a_5440_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5436_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5436_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5440_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5448_, lean_object* v_generation_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5448_, v_generation_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
lean_dec(v_a_5459_);
lean_dec_ref(v_a_5458_);
lean_dec(v_a_5457_);
lean_dec_ref(v_a_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v_a_5452_);
lean_dec(v_a_5451_);
lean_dec(v_a_5450_);
return v_res_5461_;
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
