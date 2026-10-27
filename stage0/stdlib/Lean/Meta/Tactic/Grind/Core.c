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
size_t v_x_22909__boxed_357_; lean_object* v_res_358_; 
v_x_22909__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_22909__boxed_357_, v_x_356_);
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
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v___x_444_; 
v_head_399_ = lean_ctor_get(v_as_x27_385_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_385_, 1);
v___x_401_ = lean_box(0);
v___x_444_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_399_);
if (v___x_444_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v___x_446_; 
lean_inc(v_head_399_);
v___x_446_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_399_, v___y_387_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; uint8_t v___x_448_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_448_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_toCold_450_; lean_object* v_options_451_; uint8_t v_hasTrace_452_; 
v_toCold_450_ = lean_ctor_get(v___y_395_, 0);
v_options_451_ = lean_ctor_get(v_toCold_450_, 2);
v_hasTrace_452_ = lean_ctor_get_uint8(v_options_451_, sizeof(void*)*1);
if (v_hasTrace_452_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_inheritedTraceOptions_453_ = lean_ctor_get(v_toCold_450_, 11);
v___x_454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_455_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_453_, v_options_451_, v___x_455_);
if (v___x_456_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_updateLastTag(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec_ref_known(v___x_457_, 1);
v___x_458_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_459_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_454_, v___x_460_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_dec_ref_known(v___x_461_, 1);
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
return v___x_461_;
}
}
else
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_446_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_446_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toGoalState_405_; lean_object* v_mvarId_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_443_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toGoalState_405_ = lean_ctor_get(v___x_404_, 0);
v_mvarId_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_443_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_443_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_mvarId_406_);
lean_inc(v_toGoalState_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_443_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_nextDeclIdx_410_; lean_object* v_enodeMap_411_; lean_object* v_exprs_412_; lean_object* v_parents_413_; lean_object* v_congrTable_414_; lean_object* v_appMap_415_; lean_object* v_indicesFound_416_; lean_object* v_toProcess_417_; lean_object* v_internalizing_418_; uint8_t v_inconsistent_419_; lean_object* v_nextIdx_420_; lean_object* v_newRawFacts_421_; lean_object* v_facts_422_; lean_object* v_extThms_423_; lean_object* v_ematch_424_; lean_object* v_inj_425_; lean_object* v_split_426_; lean_object* v_clean_427_; lean_object* v_sstates_428_; lean_object* v_goalStack_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_442_; 
v_nextDeclIdx_410_ = lean_ctor_get(v_toGoalState_405_, 0);
v_enodeMap_411_ = lean_ctor_get(v_toGoalState_405_, 1);
v_exprs_412_ = lean_ctor_get(v_toGoalState_405_, 2);
v_parents_413_ = lean_ctor_get(v_toGoalState_405_, 3);
v_congrTable_414_ = lean_ctor_get(v_toGoalState_405_, 4);
v_appMap_415_ = lean_ctor_get(v_toGoalState_405_, 5);
v_indicesFound_416_ = lean_ctor_get(v_toGoalState_405_, 6);
v_toProcess_417_ = lean_ctor_get(v_toGoalState_405_, 7);
v_internalizing_418_ = lean_ctor_get(v_toGoalState_405_, 8);
v_inconsistent_419_ = lean_ctor_get_uint8(v_toGoalState_405_, sizeof(void*)*19);
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
v_isSharedCheck_442_ = !lean_is_exclusive(v_toGoalState_405_);
if (v_isSharedCheck_442_ == 0)
{
v___x_431_ = v_toGoalState_405_;
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
else
{
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
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_head_399_);
v___x_433_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_411_, v_congrTable_414_, v_head_399_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 4, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_nextDeclIdx_410_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_enodeMap_411_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_exprs_412_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_parents_413_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_appMap_415_);
lean_ctor_set(v_reuseFailAlloc_441_, 6, v_indicesFound_416_);
lean_ctor_set(v_reuseFailAlloc_441_, 7, v_toProcess_417_);
lean_ctor_set(v_reuseFailAlloc_441_, 8, v_internalizing_418_);
lean_ctor_set(v_reuseFailAlloc_441_, 9, v_nextIdx_420_);
lean_ctor_set(v_reuseFailAlloc_441_, 10, v_newRawFacts_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 11, v_facts_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 12, v_extThms_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 13, v_ematch_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 14, v_inj_425_);
lean_ctor_set(v_reuseFailAlloc_441_, 15, v_split_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 16, v_clean_427_);
lean_ctor_set(v_reuseFailAlloc_441_, 17, v_sstates_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 18, v_goalStack_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*19, v_inconsistent_419_);
v___x_435_ = v_reuseFailAlloc_441_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_435_);
v___x_437_ = v___x_408_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_mvarId_406_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = lean_st_ref_put(v___y_403_, v___x_437_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_470_, v_b_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v_as_x27_470_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_Grind_getParents___redArg(v_root_484_, v_a_485_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_497_);
v___x_499_ = lean_box(0);
v___x_500_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_498_, v___x_499_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v___x_498_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_500_, 0);
lean_dec(v_unused_508_);
v___x_502_ = v___x_500_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_dec(v___x_500_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_a_497_);
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_497_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_497_);
v_a_509_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_root_517_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_530_, lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_530_, v_x_532_, v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_535_, lean_object* v_00_u03b2_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_535_, v_00_u03b2_536_, v_x_537_, v_x_538_);
lean_dec_ref(v___x_535_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_540_, v_msg_541_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec(v___y_556_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_568_, lean_object* v_as_x27_569_, lean_object* v_b_570_, lean_object* v_a_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_569_, v_b_570_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_584_, lean_object* v_as_x27_585_, lean_object* v_b_586_, lean_object* v_a_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_584_, v_as_x27_585_, v_b_586_, v_a_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec(v___y_588_);
lean_dec(v_as_x27_585_);
lean_dec(v_as_584_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_600_, lean_object* v_00_u03b2_601_, lean_object* v_x_602_, size_t v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_600_, v_x_602_, v_x_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_606_, lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v_x_23369__boxed_611_; lean_object* v_res_612_; 
v_x_23369__boxed_611_ = lean_unbox_usize(v_x_609_);
lean_dec(v_x_609_);
v_res_612_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_606_, v_00_u03b2_607_, v_x_608_, v_x_23369__boxed_611_, v_x_610_);
lean_dec_ref(v___x_606_);
return v_res_612_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_616_, lean_object* v_b_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
if (lean_obj_tag(v_as_x27_616_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_617_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_632_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; uint8_t v___x_646_; 
v_head_630_ = lean_ctor_get(v_as_x27_616_, 0);
v_tail_631_ = lean_ctor_get(v_as_x27_616_, 1);
v___x_632_ = lean_box(0);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_630_);
if (v___x_646_ == 0)
{
v_as_x27_616_ = v_tail_631_;
v_b_617_ = v___x_632_;
goto _start;
}
else
{
lean_object* v___x_648_; 
lean_inc(v_head_630_);
v___x_648_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_630_, v___y_618_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; uint8_t v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = lean_unbox(v_a_649_);
lean_dec(v_a_649_);
if (v___x_650_ == 0)
{
v_as_x27_616_ = v_tail_631_;
v_b_617_ = v___x_632_;
goto _start;
}
else
{
lean_object* v_toCold_652_; lean_object* v_options_653_; uint8_t v_hasTrace_654_; 
v_toCold_652_ = lean_ctor_get(v___y_626_, 0);
v_options_653_ = lean_ctor_get(v_toCold_652_, 2);
v_hasTrace_654_ = lean_ctor_get_uint8(v_options_653_, sizeof(void*)*1);
if (v_hasTrace_654_ == 0)
{
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
goto v___jp_633_;
}
else
{
lean_object* v_inheritedTraceOptions_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_inheritedTraceOptions_655_ = lean_ctor_get(v_toCold_652_, 11);
v___x_656_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_657_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_658_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_655_, v_options_653_, v___x_657_);
if (v___x_658_ == 0)
{
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
goto v___jp_633_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Grind_updateLastTag(v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref_known(v___x_659_, 1);
v___x_660_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_630_);
v___x_661_ = l_Lean_MessageData_ofExpr(v_head_630_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_656_, v___x_662_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
goto v___jp_633_;
}
else
{
return v___x_663_;
}
}
else
{
return v___x_659_;
}
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_664_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_648_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_648_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
v___jp_633_:
{
lean_object* v___x_644_; 
lean_inc(v_head_630_);
v___x_644_ = l_Lean_Meta_Grind_addCongrTable(v_head_630_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
v_as_x27_616_ = v_tail_631_;
v_b_617_ = v___x_632_;
goto _start;
}
else
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_672_, v_b_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v_as_x27_672_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_686_);
v___x_699_ = lean_box(0);
v___x_700_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_698_, v___x_699_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v___x_698_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_700_, 0);
lean_dec(v_unused_708_);
v___x_702_ = v___x_700_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_dec(v___x_700_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_699_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_699_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec(v_a_710_);
lean_dec(v_parents_709_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_722_, lean_object* v_as_x27_723_, lean_object* v_b_724_, lean_object* v_a_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_723_, v_b_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_738_, lean_object* v_as_x27_739_, lean_object* v_b_740_, lean_object* v_a_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_738_, v_as_x27_739_, v_b_740_, v_a_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v_as_x27_739_);
lean_dec(v_as_738_);
return v_res_753_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_754_, lean_object* v_i_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_keys_754_);
v___x_758_ = lean_nat_dec_lt(v_i_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_i_755_);
return v___x_758_;
}
else
{
lean_object* v_k_x27_759_; uint8_t v___x_760_; 
v_k_x27_759_ = lean_array_fget_borrowed(v_keys_754_, v_i_755_);
v___x_760_ = l_Lean_instBEqMVarId_beq(v_k_756_, v_k_x27_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_i_755_, v___x_761_);
lean_dec(v_i_755_);
v_i_755_ = v___x_762_;
goto _start;
}
else
{
lean_dec(v_i_755_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_764_, lean_object* v_i_765_, lean_object* v_k_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_764_, v_i_765_, v_k_766_);
lean_dec(v_k_766_);
lean_dec_ref(v_keys_764_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_769_, size_t v_x_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v_es_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_j_776_; lean_object* v___x_777_; 
v_es_772_ = lean_ctor_get(v_x_769_, 0);
v___x_773_ = lean_box(2);
v___x_774_ = ((size_t)31ULL);
v___x_775_ = lean_usize_land(v_x_770_, v___x_774_);
v_j_776_ = lean_usize_to_nat(v___x_775_);
v___x_777_ = lean_array_get_borrowed(v___x_773_, v_es_772_, v_j_776_);
lean_dec(v_j_776_);
switch(lean_obj_tag(v___x_777_))
{
case 0:
{
lean_object* v_key_778_; uint8_t v___x_779_; 
v_key_778_ = lean_ctor_get(v___x_777_, 0);
v___x_779_ = l_Lean_instBEqMVarId_beq(v_x_771_, v_key_778_);
return v___x_779_;
}
case 1:
{
lean_object* v_node_780_; size_t v___x_781_; size_t v___x_782_; 
v_node_780_ = lean_ctor_get(v___x_777_, 0);
v___x_781_ = ((size_t)5ULL);
v___x_782_ = lean_usize_shift_right(v_x_770_, v___x_781_);
v_x_769_ = v_node_780_;
v_x_770_ = v___x_782_;
goto _start;
}
default: 
{
uint8_t v___x_784_; 
v___x_784_ = 0;
return v___x_784_;
}
}
}
else
{
lean_object* v_ks_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_ks_785_ = lean_ctor_get(v_x_769_, 0);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_785_, v___x_786_, v_x_771_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
size_t v_x_9681__boxed_791_; uint8_t v_res_792_; lean_object* v_r_793_; 
v_x_9681__boxed_791_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_788_, v_x_9681__boxed_791_, v_x_790_);
lean_dec(v_x_790_);
lean_dec_ref(v_x_788_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
uint64_t v___x_796_; size_t v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Lean_instHashableMVarId_hash(v_x_795_);
v___x_797_ = lean_uint64_to_usize(v___x_796_);
v___x_798_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_794_, v___x_797_, v_x_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_799_, v_x_800_);
lean_dec(v_x_800_);
lean_dec_ref(v_x_799_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_mctx_807_; lean_object* v_eAssignment_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_806_ = lean_st_ref_get(v___y_804_);
v_mctx_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_ref(v_mctx_807_);
lean_dec(v___x_806_);
v_eAssignment_808_ = lean_ctor_get(v_mctx_807_, 8);
lean_inc_ref(v_eAssignment_808_);
lean_dec_ref(v_mctx_807_);
v___x_809_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_808_, v_mvarId_803_);
lean_dec_ref(v_eAssignment_808_);
v___x_810_ = lean_box(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec(v_mvarId_812_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_826_ = l_Lean_mkConst(v___x_825_, v___x_824_);
return v___x_826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_box(0);
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_834_ = l_Lean_mkConst(v___x_833_, v___x_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_mvarId_847_; lean_object* v___x_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_902_; 
v___x_846_ = lean_st_ref_get(v_a_835_);
v_mvarId_847_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_mvarId_847_);
lean_dec(v___x_846_);
v___x_848_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_847_, v_a_842_);
lean_dec(v_mvarId_847_);
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_902_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_902_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_902_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; 
v___x_853_ = lean_unbox(v_a_849_);
lean_dec(v_a_849_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_del_object(v___x_851_);
v___x_854_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_839_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_855_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_839_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_839_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_864_ = l_Lean_mkApp4(v___x_862_, v_a_859_, v_a_861_, v_a_857_, v___x_863_);
v___x_865_ = l_Lean_Meta_Grind_closeGoal(v___x_864_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_865_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_859_);
lean_dec(v_a_857_);
v_a_866_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_860_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_860_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_857_);
v_a_874_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_858_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_858_);
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
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_a_882_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_856_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_856_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_854_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_854_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_898_);
v___x_900_ = v___x_851_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec(v_a_903_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_915_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v_mvarId_928_);
return v_res_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_942_, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v_res_948_; lean_object* v_r_949_; 
v_res_948_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_945_, v_x_946_, v_x_947_);
lean_dec(v_x_947_);
lean_dec_ref(v_x_946_);
v_r_949_ = lean_box(v_res_948_);
return v_r_949_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, size_t v_x_952_, lean_object* v_x_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_951_, v_x_952_, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
size_t v_x_9964__boxed_959_; uint8_t v_res_960_; lean_object* v_r_961_; 
v_x_9964__boxed_959_ = lean_unbox_usize(v_x_957_);
lean_dec(v_x_957_);
v_res_960_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_955_, v_x_956_, v_x_9964__boxed_959_, v_x_958_);
lean_dec(v_x_958_);
lean_dec_ref(v_x_956_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_heq_965_, lean_object* v_i_966_, lean_object* v_k_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_963_, v_i_966_, v_k_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_969_, lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_heq_972_, lean_object* v_i_973_, lean_object* v_k_974_){
_start:
{
uint8_t v_res_975_; lean_object* v_r_976_; 
v_res_975_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_969_, v_keys_970_, v_vals_971_, v_heq_972_, v_i_973_, v_k_974_);
lean_dec(v_k_974_);
lean_dec_ref(v_vals_971_);
lean_dec_ref(v_keys_970_);
v_r_976_ = lean_box(v_res_975_);
return v_r_976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_982_ = l_Lean_mkConst(v___x_981_, v___x_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_983_, lean_object* v_rhs_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
lean_inc_ref(v_rhs_984_);
lean_inc_ref(v_lhs_983_);
v___x_996_ = l_Lean_Meta_mkEq(v_lhs_983_, v_rhs_984_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
lean_inc(v_a_994_);
lean_inc_ref(v_a_993_);
lean_inc(v_a_992_);
lean_inc_ref(v_a_991_);
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc(v_a_986_);
lean_inc(v_a_985_);
v___x_998_ = lean_grind_mk_eq_proof(v_lhs_983_, v_rhs_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
lean_inc(v_a_997_);
v___x_1000_ = l_Lean_Meta_mkDecide(v_a_997_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1003_ = l_Lean_Expr_appArg_x21(v_a_1001_);
lean_dec(v_a_1001_);
v___x_1004_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_997_);
v___x_1005_ = l_Lean_mkApp3(v___x_1002_, v_a_997_, v___x_1003_, v___x_1004_);
v___x_1006_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_989_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1009_ = l_Lean_mkApp4(v___x_1008_, v_a_997_, v_a_1007_, v___x_1005_, v_a_999_);
v___x_1010_ = l_Lean_Meta_Grind_closeGoal(v___x_1009_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_1010_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___x_1005_);
lean_dec(v_a_999_);
lean_dec(v_a_997_);
v_a_1011_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1006_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1006_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_a_999_);
lean_dec(v_a_997_);
v_a_1019_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1000_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1000_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_a_997_);
v_a_1027_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_998_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_998_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_rhs_984_);
lean_dec_ref(v_lhs_983_);
v_a_1035_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_996_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_996_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1043_, lean_object* v_rhs_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1043_, v_rhs_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1057_, lean_object* v_as_x27_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
if (lean_obj_tag(v_as_x27_1058_) == 0)
{
lean_object* v___x_1071_; 
lean_dec(v___x_1057_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_b_1059_);
return v___x_1071_;
}
else
{
lean_object* v_head_1072_; lean_object* v_tail_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_head_1072_ = lean_ctor_get(v_as_x27_1058_, 0);
v_tail_1073_ = lean_ctor_get(v_as_x27_1058_, 1);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_st_ref_get(v___y_1060_);
lean_inc(v_head_1072_);
v___x_1076_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1075_, v_head_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_self_1078_; lean_object* v_next_1079_; lean_object* v_root_1080_; lean_object* v_congr_1081_; lean_object* v_target_x3f_1082_; lean_object* v_proof_x3f_1083_; uint8_t v_flipped_1084_; lean_object* v_size_1085_; uint8_t v_interpreted_1086_; uint8_t v_ctor_1087_; uint8_t v_hasLambdas_1088_; uint8_t v_heqProofs_1089_; lean_object* v_idx_1090_; lean_object* v_generation_1091_; lean_object* v_mt_1092_; lean_object* v_sTerms_1093_; uint8_t v_funCC_1094_; lean_object* v_ematchDiagSource_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1107_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v_self_1078_ = lean_ctor_get(v_a_1077_, 0);
v_next_1079_ = lean_ctor_get(v_a_1077_, 1);
v_root_1080_ = lean_ctor_get(v_a_1077_, 2);
v_congr_1081_ = lean_ctor_get(v_a_1077_, 3);
v_target_x3f_1082_ = lean_ctor_get(v_a_1077_, 4);
v_proof_x3f_1083_ = lean_ctor_get(v_a_1077_, 5);
v_flipped_1084_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12);
v_size_1085_ = lean_ctor_get(v_a_1077_, 6);
v_interpreted_1086_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12 + 1);
v_ctor_1087_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12 + 2);
v_hasLambdas_1088_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12 + 3);
v_heqProofs_1089_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12 + 4);
v_idx_1090_ = lean_ctor_get(v_a_1077_, 7);
v_generation_1091_ = lean_ctor_get(v_a_1077_, 8);
v_mt_1092_ = lean_ctor_get(v_a_1077_, 9);
v_sTerms_1093_ = lean_ctor_get(v_a_1077_, 10);
v_funCC_1094_ = lean_ctor_get_uint8(v_a_1077_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1095_ = lean_ctor_get(v_a_1077_, 11);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1097_ = v_a_1077_;
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_ematchDiagSource_1095_);
lean_inc(v_sTerms_1093_);
lean_inc(v_mt_1092_);
lean_inc(v_generation_1091_);
lean_inc(v_idx_1090_);
lean_inc(v_size_1085_);
lean_inc(v_proof_x3f_1083_);
lean_inc(v_target_x3f_1082_);
lean_inc(v_congr_1081_);
lean_inc(v_root_1080_);
lean_inc(v_next_1079_);
lean_inc(v_self_1078_);
lean_dec(v_a_1077_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1107_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_nat_dec_lt(v_mt_1092_, v___x_1057_);
lean_dec(v_mt_1092_);
if (v___x_1099_ == 0)
{
lean_del_object(v___x_1097_);
lean_dec(v_ematchDiagSource_1095_);
lean_dec(v_sTerms_1093_);
lean_dec(v_generation_1091_);
lean_dec(v_idx_1090_);
lean_dec(v_size_1085_);
lean_dec(v_proof_x3f_1083_);
lean_dec(v_target_x3f_1082_);
lean_dec_ref(v_congr_1081_);
lean_dec_ref(v_root_1080_);
lean_dec_ref(v_next_1079_);
lean_dec_ref(v_self_1078_);
v_as_x27_1058_ = v_tail_1073_;
v_b_1059_ = v___x_1074_;
goto _start;
}
else
{
lean_object* v___x_1102_; 
lean_inc(v___x_1057_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 9, v___x_1057_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_self_1078_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_next_1079_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_root_1080_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_congr_1081_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_target_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1106_, 5, v_proof_x3f_1083_);
lean_ctor_set(v_reuseFailAlloc_1106_, 6, v_size_1085_);
lean_ctor_set(v_reuseFailAlloc_1106_, 7, v_idx_1090_);
lean_ctor_set(v_reuseFailAlloc_1106_, 8, v_generation_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 9, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1106_, 10, v_sTerms_1093_);
lean_ctor_set(v_reuseFailAlloc_1106_, 11, v_ematchDiagSource_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12, v_flipped_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12 + 1, v_interpreted_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12 + 2, v_ctor_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12 + 3, v_hasLambdas_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12 + 4, v_heqProofs_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*12 + 5, v_funCC_1094_);
v___x_1102_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
lean_inc(v_head_1072_);
v___x_1103_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1072_, v___x_1102_, v___y_1060_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref_known(v___x_1103_, 1);
v___x_1104_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1072_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec_ref_known(v___x_1104_, 1);
v_as_x27_1058_ = v_tail_1073_;
v_b_1059_ = v___x_1074_;
goto _start;
}
else
{
lean_dec(v___x_1057_);
return v___x_1104_;
}
}
else
{
lean_dec(v___x_1057_);
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___x_1057_);
v_a_1108_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1076_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1076_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_toGoalState_1129_; lean_object* v_ematch_1130_; lean_object* v_gmt_1131_; lean_object* v___x_1132_; 
v___x_1128_ = lean_st_ref_get(v_a_1117_);
v_toGoalState_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_toGoalState_1129_);
lean_dec(v___x_1128_);
v_ematch_1130_ = lean_ctor_get(v_toGoalState_1129_, 13);
lean_inc_ref(v_ematch_1130_);
lean_dec_ref(v_toGoalState_1129_);
v_gmt_1131_ = lean_ctor_get(v_ematch_1130_, 1);
lean_inc(v_gmt_1131_);
lean_dec_ref(v_ematch_1130_);
v___x_1132_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1133_);
lean_dec(v_a_1133_);
v___x_1135_ = lean_box(0);
v___x_1136_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1131_, v___x_1134_, v___x_1135_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v___x_1134_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1136_, 0);
lean_dec(v_unused_1144_);
v___x_1138_ = v___x_1136_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v___x_1136_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1135_);
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1135_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
return v___x_1136_;
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_gmt_1131_);
v_a_1145_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1132_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1132_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_root_1153_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1166_, lean_object* v_as_x27_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1166_, v_as_x27_1167_, v_b_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v_as_x27_1167_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1181_, lean_object* v_as_1182_, lean_object* v_as_x27_1183_, lean_object* v_b_1184_, lean_object* v_a_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1181_, v_as_x27_1183_, v_b_1184_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1198_, lean_object* v_as_1199_, lean_object* v_as_x27_1200_, lean_object* v_b_1201_, lean_object* v_a_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1198_, v_as_1199_, v_as_x27_1200_, v_b_1201_, v_a_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec(v_as_x27_1200_);
lean_dec(v_as_1199_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
if (lean_obj_tag(v_a_1215_) == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = l_List_reverse___redArg(v_a_1216_);
return v___x_1217_;
}
else
{
lean_object* v_head_1218_; lean_object* v_tail_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
v_head_1218_ = lean_ctor_get(v_a_1215_, 0);
v_tail_1219_ = lean_ctor_get(v_a_1215_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_a_1215_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v_a_1215_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_tail_1219_);
lean_inc(v_head_1218_);
lean_dec(v_a_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_MessageData_ofExpr(v_head_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_a_1216_);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_a_1216_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v_a_1215_ = v_tail_1219_;
v_a_1216_ = v___x_1225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1229_, lean_object* v_a_1230_, lean_object* v_fst_1231_, lean_object* v_a_1232_, lean_object* v_lams_1233_, lean_object* v_____r_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1229_, v_a_1232_, v___y_1235_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = lean_unbox(v_a_1284_);
lean_dec(v_a_1284_);
if (v___x_1285_ == 0)
{
goto v___jp_1246_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_inc(v_fst_1231_);
v___x_1286_ = l_Array_reverse___redArg(v_fst_1231_);
lean_inc(v_snd_1229_);
v___x_1287_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1233_, v_snd_1229_, v___x_1286_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec_ref_known(v___x_1287_, 1);
goto v___jp_1246_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_fst_1231_);
lean_dec(v_snd_1229_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_fst_1231_);
lean_dec(v_snd_1229_);
v_a_1296_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1283_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1283_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
v___jp_1246_:
{
if (lean_obj_tag(v_snd_1229_) == 5)
{
lean_object* v_fn_1247_; lean_object* v_arg_1248_; lean_object* v___x_1249_; 
v_fn_1247_ = lean_ctor_get(v_snd_1229_, 0);
lean_inc_ref(v_fn_1247_);
v_arg_1248_ = lean_ctor_get(v_snd_1229_, 1);
lean_inc_ref(v_arg_1248_);
v___x_1249_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1230_, v___y_1235_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_box(0);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc(v___y_1235_);
v___x_1252_ = lean_grind_internalize(v_snd_1229_, v_a_1250_, v___x_1251_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1252_, 0);
lean_dec(v_unused_1263_);
v___x_1254_ = v___x_1252_;
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v___x_1252_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1256_ = lean_array_push(v_fst_1231_, v_arg_1248_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v_fn_1247_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1258_);
v___x_1260_ = v___x_1254_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_arg_1248_);
lean_dec_ref(v_fn_1247_);
lean_dec(v_fst_1231_);
v_a_1264_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1252_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1252_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_arg_1248_);
lean_dec_ref_known(v_snd_1229_, 2);
lean_dec_ref(v_fn_1247_);
lean_dec(v_fst_1231_);
v_a_1272_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1249_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1249_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_fst_1231_);
lean_ctor_set(v___x_1280_, 1, v_snd_1229_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1304_ = _args[0];
lean_object* v_a_1305_ = _args[1];
lean_object* v_fst_1306_ = _args[2];
lean_object* v_a_1307_ = _args[3];
lean_object* v_lams_1308_ = _args[4];
lean_object* v_____r_1309_ = _args[5];
lean_object* v___y_1310_ = _args[6];
lean_object* v___y_1311_ = _args[7];
lean_object* v___y_1312_ = _args[8];
lean_object* v___y_1313_ = _args[9];
lean_object* v___y_1314_ = _args[10];
lean_object* v___y_1315_ = _args[11];
lean_object* v___y_1316_ = _args[12];
lean_object* v___y_1317_ = _args[13];
lean_object* v___y_1318_ = _args[14];
lean_object* v___y_1319_ = _args[15];
lean_object* v___y_1320_ = _args[16];
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1304_, v_a_1305_, v_fst_1306_, v_a_1307_, v_lams_1308_, v_____r_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v_lams_1308_);
lean_dec_ref(v_a_1307_);
lean_dec_ref(v_a_1305_);
return v_res_1321_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1329_ = l_Lean_Name_append(v___x_1328_, v___x_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_lams_1335_, lean_object* v_a_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___y_1349_; lean_object* v_toCold_1369_; lean_object* v_options_1370_; lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1409_; 
v_toCold_1369_ = lean_ctor_get(v___y_1345_, 0);
v_options_1370_ = lean_ctor_get(v_toCold_1369_, 2);
v_fst_1371_ = lean_ctor_get(v_a_1336_, 0);
v_snd_1372_ = lean_ctor_get(v_a_1336_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1374_ = v_a_1336_;
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_a_1336_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
v___jp_1348_:
{
if (lean_obj_tag(v___y_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1360_; 
v_a_1350_ = lean_ctor_get(v___y_1349_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___y_1349_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1352_ = v___y_1349_;
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___y_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
if (lean_obj_tag(v_a_1350_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; 
v_a_1354_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v_a_1350_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_a_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
else
{
lean_object* v_a_1358_; 
lean_del_object(v___x_1352_);
v_a_1358_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_a_1350_, 1);
v_a_1336_ = v_a_1358_;
goto _start;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_a_1361_ = lean_ctor_get(v___y_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___y_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___y_1349_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___y_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
v_resetjp_1373_:
{
lean_object* v_inheritedTraceOptions_1376_; uint8_t v_hasTrace_1377_; 
v_inheritedTraceOptions_1376_ = lean_ctor_get(v_toCold_1369_, 11);
v_hasTrace_1377_ = lean_ctor_get_uint8(v_options_1370_, sizeof(void*)*1);
if (v_hasTrace_1377_ == 0)
{
lean_del_object(v___x_1374_);
goto v___jp_1378_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1381_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1382_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1383_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1376_, v_options_1370_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_del_object(v___x_1374_);
goto v___jp_1378_;
}
else
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Meta_Grind_updateLastTag(v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec_ref_known(v___x_1384_, 1);
v___x_1385_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1372_);
v___x_1386_ = l_Lean_MessageData_ofExpr(v_snd_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 7);
lean_ctor_set(v___x_1374_, 1, v___x_1386_);
lean_ctor_set(v___x_1374_, 0, v___x_1385_);
v___x_1388_ = v___x_1374_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1381_, v___x_1388_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1372_, v_a_1333_, v_fst_1371_, v_a_1334_, v_lams_1335_, v_a_1390_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
v___y_1349_ = v___x_1391_;
goto v___jp_1348_;
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
v_a_1392_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1389_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1389_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_del_object(v___x_1374_);
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
v_a_1401_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1384_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1384_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
v___jp_1378_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1372_, v_a_1333_, v_fst_1371_, v_a_1334_, v_lams_1335_, v___x_1379_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
v___y_1349_ = v___x_1380_;
goto v___jp_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_lams_1412_, lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1410_, v_a_1411_, v_lams_1412_, v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v_lams_1412_);
lean_dec_ref(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1425_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1430_ = l_Lean_stringToMessageData(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1431_, lean_object* v_lams_1432_, lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
if (lean_obj_tag(v_as_x27_1433_) == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1434_);
return v___x_1446_;
}
else
{
lean_object* v_toCold_1447_; lean_object* v_options_1448_; lean_object* v_head_1449_; lean_object* v_tail_1450_; lean_object* v_inheritedTraceOptions_1451_; uint8_t v_hasTrace_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; 
v_toCold_1447_ = lean_ctor_get(v___y_1443_, 0);
v_options_1448_ = lean_ctor_get(v_toCold_1447_, 2);
v_head_1449_ = lean_ctor_get(v_as_x27_1433_, 0);
v_tail_1450_ = lean_ctor_get(v_as_x27_1433_, 1);
v_inheritedTraceOptions_1451_ = lean_ctor_get(v_toCold_1447_, 11);
v_hasTrace_1452_ = lean_ctor_get_uint8(v_options_1448_, sizeof(void*)*1);
v___x_1453_ = lean_box(0);
v___x_1454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1452_ == 0)
{
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1478_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1451_, v_options_1448_, v___x_1478_);
if (v___x_1479_ == 0)
{
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Meta_Grind_updateLastTag(v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref_known(v___x_1480_, 1);
v___x_1481_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1449_);
v___x_1482_ = l_Lean_MessageData_ofExpr(v_head_1449_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1477_, v___x_1483_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref_known(v___x_1484_, 1);
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
goto v___jp_1455_;
}
else
{
return v___x_1484_;
}
}
else
{
return v___x_1480_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_inc(v_head_1449_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1454_);
lean_ctor_set(v___x_1466_, 1, v_head_1449_);
v___x_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1449_, v_a_1431_, v_lams_1432_, v___x_1466_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v_as_x27_1433_ = v_tail_1450_;
v_b_1434_ = v___x_1453_;
goto _start;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1485_, lean_object* v_lams_1486_, lean_object* v_as_x27_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1485_, v_lams_1486_, v_as_x27_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_as_x27_1487_);
lean_dec_ref(v_lams_1486_);
lean_dec_ref(v_a_1485_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1501_, lean_object* v_lams_1502_, lean_object* v_as_1503_, lean_object* v_as_x27_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
if (lean_obj_tag(v_as_x27_1504_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_b_1505_);
return v___x_1517_;
}
else
{
lean_object* v_toCold_1518_; lean_object* v_options_1519_; lean_object* v_head_1520_; lean_object* v_tail_1521_; lean_object* v_inheritedTraceOptions_1522_; uint8_t v_hasTrace_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; 
v_toCold_1518_ = lean_ctor_get(v___y_1514_, 0);
v_options_1519_ = lean_ctor_get(v_toCold_1518_, 2);
v_head_1520_ = lean_ctor_get(v_as_x27_1504_, 0);
v_tail_1521_ = lean_ctor_get(v_as_x27_1504_, 1);
v_inheritedTraceOptions_1522_ = lean_ctor_get(v_toCold_1518_, 11);
v_hasTrace_1523_ = lean_ctor_get_uint8(v_options_1519_, sizeof(void*)*1);
v___x_1524_ = lean_box(0);
v___x_1525_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1523_ == 0)
{
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1549_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1522_, v_options_1519_, v___x_1549_);
if (v___x_1550_ == 0)
{
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Grind_updateLastTag(v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec_ref_known(v___x_1551_, 1);
v___x_1552_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1520_);
v___x_1553_ = l_Lean_MessageData_ofExpr(v_head_1520_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1548_, v___x_1554_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_dec_ref_known(v___x_1555_, 1);
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
v___y_1533_ = v___y_1512_;
v___y_1534_ = v___y_1513_;
v___y_1535_ = v___y_1514_;
v___y_1536_ = v___y_1515_;
goto v___jp_1526_;
}
else
{
return v___x_1555_;
}
}
else
{
return v___x_1551_;
}
}
}
v___jp_1526_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc(v_head_1520_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1525_);
lean_ctor_set(v___x_1537_, 1, v_head_1520_);
v___x_1538_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1520_, v_a_1501_, v_lams_1502_, v___x_1537_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref_known(v___x_1538_, 1);
v___x_1539_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1501_, v_lams_1502_, v_tail_1521_, v___x_1524_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1539_;
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1538_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1538_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1556_, lean_object* v_lams_1557_, lean_object* v_as_1558_, lean_object* v_as_x27_1559_, lean_object* v_b_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1556_, v_lams_1557_, v_as_1558_, v_as_x27_1559_, v_b_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec(v_as_x27_1559_);
lean_dec(v_as_1558_);
lean_dec_ref(v_lams_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1572_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1579_, lean_object* v_lams_1580_, lean_object* v_as_1581_, size_t v_sz_1582_, size_t v_i_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_usize_dec_lt(v_i_1583_, v_sz_1582_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_b_1584_);
return v___x_1597_;
}
else
{
lean_object* v_toCold_1598_; lean_object* v_options_1599_; lean_object* v_inheritedTraceOptions_1600_; uint8_t v_hasTrace_1601_; lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; 
v_toCold_1598_ = lean_ctor_get(v___y_1593_, 0);
v_options_1599_ = lean_ctor_get(v_toCold_1598_, 2);
v_inheritedTraceOptions_1600_ = lean_ctor_get(v_toCold_1598_, 11);
v_hasTrace_1601_ = lean_ctor_get_uint8(v_options_1599_, sizeof(void*)*1);
v___x_1602_ = lean_box(0);
v_a_1603_ = lean_array_uget_borrowed(v_as_1581_, v_i_1583_);
if (v_hasTrace_1601_ == 0)
{
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1631_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1632_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1600_, v_options_1599_, v___x_1631_);
if (v___x_1632_ == 0)
{
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Grind_updateLastTag(v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1633_, 1);
v___x_1634_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1603_, v___y_1585_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1603_);
v___x_1637_ = l_Lean_MessageData_ofExpr(v_a_1603_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1635_);
lean_dec(v_a_1635_);
v___x_1642_ = lean_box(0);
v___x_1643_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1641_, v___x_1642_);
v___x_1644_ = l_Lean_MessageData_ofList(v___x_1643_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1640_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1630_, v___x_1645_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec_ref_known(v___x_1646_, 1);
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
v___y_1611_ = v___y_1591_;
v___y_1612_ = v___y_1592_;
v___y_1613_ = v___y_1593_;
v___y_1614_ = v___y_1594_;
goto v___jp_1604_;
}
else
{
return v___x_1646_;
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1634_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1634_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
return v___x_1633_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1603_, v___y_1605_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1616_);
lean_dec(v_a_1616_);
v___x_1618_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1579_, v_lams_1580_, v___x_1617_, v___x_1617_, v___x_1602_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___x_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
size_t v___x_1619_; size_t v___x_1620_; 
lean_dec_ref_known(v___x_1618_, 1);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_add(v_i_1583_, v___x_1619_);
v_i_1583_ = v___x_1620_;
v_b_1584_ = v___x_1602_;
goto _start;
}
else
{
return v___x_1618_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1615_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1615_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1655_ = _args[0];
lean_object* v_lams_1656_ = _args[1];
lean_object* v_as_1657_ = _args[2];
lean_object* v_sz_1658_ = _args[3];
lean_object* v_i_1659_ = _args[4];
lean_object* v_b_1660_ = _args[5];
lean_object* v___y_1661_ = _args[6];
lean_object* v___y_1662_ = _args[7];
lean_object* v___y_1663_ = _args[8];
lean_object* v___y_1664_ = _args[9];
lean_object* v___y_1665_ = _args[10];
lean_object* v___y_1666_ = _args[11];
lean_object* v___y_1667_ = _args[12];
lean_object* v___y_1668_ = _args[13];
lean_object* v___y_1669_ = _args[14];
lean_object* v___y_1670_ = _args[15];
lean_object* v___y_1671_ = _args[16];
_start:
{
size_t v_sz_boxed_1672_; size_t v_i_boxed_1673_; lean_object* v_res_1674_; 
v_sz_boxed_1672_ = lean_unbox_usize(v_sz_1658_);
lean_dec(v_sz_1658_);
v_i_boxed_1673_ = lean_unbox_usize(v_i_1659_);
lean_dec(v_i_1659_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1655_, v_lams_1656_, v_as_1657_, v_sz_boxed_1672_, v_i_boxed_1673_, v_b_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v_as_1657_);
lean_dec_ref(v_lams_1656_);
lean_dec_ref(v_a_1655_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1675_, lean_object* v_lams_1676_, lean_object* v_as_1677_, size_t v_sz_1678_, size_t v_i_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_lt(v_i_1679_, v_sz_1678_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1680_);
return v___x_1693_;
}
else
{
lean_object* v_toCold_1694_; lean_object* v_options_1695_; lean_object* v_inheritedTraceOptions_1696_; uint8_t v_hasTrace_1697_; lean_object* v___x_1698_; lean_object* v_a_1699_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; 
v_toCold_1694_ = lean_ctor_get(v___y_1689_, 0);
v_options_1695_ = lean_ctor_get(v_toCold_1694_, 2);
v_inheritedTraceOptions_1696_ = lean_ctor_get(v_toCold_1694_, 11);
v_hasTrace_1697_ = lean_ctor_get_uint8(v_options_1695_, sizeof(void*)*1);
v___x_1698_ = lean_box(0);
v_a_1699_ = lean_array_uget_borrowed(v_as_1677_, v_i_1679_);
if (v_hasTrace_1697_ == 0)
{
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1727_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1696_, v_options_1695_, v___x_1727_);
if (v___x_1728_ == 0)
{
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_Grind_updateLastTag(v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref_known(v___x_1729_, 1);
v___x_1730_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1699_, v___y_1681_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1699_);
v___x_1733_ = l_Lean_MessageData_ofExpr(v_a_1699_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1731_);
lean_dec(v_a_1731_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1737_, v___x_1738_);
v___x_1740_ = l_Lean_MessageData_ofList(v___x_1739_);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1736_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1726_, v___x_1741_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_dec_ref_known(v___x_1742_, 1);
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
v___y_1707_ = v___y_1687_;
v___y_1708_ = v___y_1688_;
v___y_1709_ = v___y_1689_;
v___y_1710_ = v___y_1690_;
goto v___jp_1700_;
}
else
{
return v___x_1742_;
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
v_a_1743_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1730_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1730_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
else
{
return v___x_1729_;
}
}
}
v___jp_1700_:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1699_, v___y_1701_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1713_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1712_);
lean_dec(v_a_1712_);
v___x_1714_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1675_, v_lams_1676_, v___x_1713_, v___x_1713_, v___x_1698_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___x_1713_);
if (lean_obj_tag(v___x_1714_) == 0)
{
size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1714_, 1);
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1679_, v___x_1715_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1675_, v_lams_1676_, v_as_1677_, v_sz_1678_, v___x_1716_, v___x_1698_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1717_;
}
else
{
return v___x_1714_;
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1711_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1711_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1751_ = _args[0];
lean_object* v_lams_1752_ = _args[1];
lean_object* v_as_1753_ = _args[2];
lean_object* v_sz_1754_ = _args[3];
lean_object* v_i_1755_ = _args[4];
lean_object* v_b_1756_ = _args[5];
lean_object* v___y_1757_ = _args[6];
lean_object* v___y_1758_ = _args[7];
lean_object* v___y_1759_ = _args[8];
lean_object* v___y_1760_ = _args[9];
lean_object* v___y_1761_ = _args[10];
lean_object* v___y_1762_ = _args[11];
lean_object* v___y_1763_ = _args[12];
lean_object* v___y_1764_ = _args[13];
lean_object* v___y_1765_ = _args[14];
lean_object* v___y_1766_ = _args[15];
lean_object* v___y_1767_ = _args[16];
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1751_, v_lams_1752_, v_as_1753_, v_sz_boxed_1768_, v_i_boxed_1769_, v_b_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v_as_1753_);
lean_dec_ref(v_lams_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1777_, lean_object* v_fns_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = lean_array_get_size(v_lams_1777_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_nat_dec_eq(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1793_ = l_Lean_instInhabitedExpr;
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_sub(v___x_1790_, v___x_1794_);
v___x_1796_ = lean_array_get_borrowed(v___x_1793_, v_lams_1777_, v___x_1795_);
lean_dec(v___x_1795_);
v___x_1797_ = lean_st_ref_get(v_a_1779_);
lean_inc(v___x_1796_);
v___x_1798_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1797_, v___x_1796_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v___x_1797_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v_toCold_1823_; lean_object* v_options_1824_; uint8_t v_hasTrace_1825_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v_toCold_1823_ = lean_ctor_get(v_a_1787_, 0);
v_options_1824_ = lean_ctor_get(v_toCold_1823_, 2);
v_hasTrace_1825_ = lean_ctor_get_uint8(v_options_1824_, sizeof(void*)*1);
if (v_hasTrace_1825_ == 0)
{
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
goto v___jp_1800_;
}
else
{
lean_object* v_inheritedTraceOptions_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v_inheritedTraceOptions_1826_ = lean_ctor_get(v_toCold_1823_, 11);
v___x_1827_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1828_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1826_, v_options_1824_, v___x_1828_);
if (v___x_1829_ == 0)
{
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Meta_Grind_updateLastTag(v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec_ref_known(v___x_1830_, 1);
v___x_1831_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1778_);
v___x_1832_ = lean_array_to_list(v_fns_1778_);
v___x_1833_ = lean_box(0);
v___x_1834_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1832_, v___x_1833_);
v___x_1835_ = l_Lean_MessageData_ofList(v___x_1834_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1831_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_inc_ref(v_lams_1777_);
v___x_1839_ = lean_array_to_list(v_lams_1777_);
v___x_1840_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1839_, v___x_1833_);
v___x_1841_ = l_Lean_MessageData_ofList(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1838_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1827_, v___x_1842_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_dec_ref_known(v___x_1843_, 1);
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
v___y_1807_ = v_a_1785_;
v___y_1808_ = v_a_1786_;
v___y_1809_ = v_a_1787_;
v___y_1810_ = v_a_1788_;
goto v___jp_1800_;
}
else
{
lean_dec(v_a_1799_);
lean_dec_ref(v_fns_1778_);
lean_dec_ref(v_lams_1777_);
return v___x_1843_;
}
}
else
{
lean_dec(v_a_1799_);
lean_dec_ref(v_fns_1778_);
lean_dec_ref(v_lams_1777_);
return v___x_1830_;
}
}
}
v___jp_1800_:
{
lean_object* v___x_1811_; size_t v_sz_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1811_ = lean_box(0);
v_sz_1812_ = lean_array_size(v_fns_1778_);
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1799_, v_lams_1777_, v_fns_1778_, v_sz_1812_, v___x_1813_, v___x_1811_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v_fns_1778_);
lean_dec_ref(v_lams_1777_);
lean_dec(v_a_1799_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1814_, 0);
lean_dec(v_unused_1822_);
v___x_1816_ = v___x_1814_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v___x_1814_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1811_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1811_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_fns_1778_);
lean_dec_ref(v_lams_1777_);
v_a_1844_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1798_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1798_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v_fns_1778_);
lean_dec_ref(v_lams_1777_);
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1854_, lean_object* v_fns_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1854_, v_fns_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1856_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_lams_1870_, lean_object* v_inst_1871_, lean_object* v_a_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1868_, v_a_1869_, v_lams_1870_, v_a_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_lams_1887_, lean_object* v_inst_1888_, lean_object* v_a_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1885_, v_a_1886_, v_lams_1887_, v_inst_1888_, v_a_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v_lams_1887_);
lean_dec_ref(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1902_, lean_object* v_lams_1903_, lean_object* v_as_1904_, lean_object* v_as_x27_1905_, lean_object* v_b_1906_, lean_object* v_a_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1902_, v_lams_1903_, v_as_1904_, v_as_x27_1905_, v_b_1906_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1920_ = _args[0];
lean_object* v_lams_1921_ = _args[1];
lean_object* v_as_1922_ = _args[2];
lean_object* v_as_x27_1923_ = _args[3];
lean_object* v_b_1924_ = _args[4];
lean_object* v_a_1925_ = _args[5];
lean_object* v___y_1926_ = _args[6];
lean_object* v___y_1927_ = _args[7];
lean_object* v___y_1928_ = _args[8];
lean_object* v___y_1929_ = _args[9];
lean_object* v___y_1930_ = _args[10];
lean_object* v___y_1931_ = _args[11];
lean_object* v___y_1932_ = _args[12];
lean_object* v___y_1933_ = _args[13];
lean_object* v___y_1934_ = _args[14];
lean_object* v___y_1935_ = _args[15];
lean_object* v___y_1936_ = _args[16];
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1920_, v_lams_1921_, v_as_1922_, v_as_x27_1923_, v_b_1924_, v_a_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v_as_x27_1923_);
lean_dec(v_as_1922_);
lean_dec_ref(v_lams_1921_);
lean_dec_ref(v_a_1920_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1938_, lean_object* v_lams_1939_, lean_object* v_as_1940_, lean_object* v_as_x27_1941_, lean_object* v_b_1942_, lean_object* v_a_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1938_, v_lams_1939_, v_as_x27_1941_, v_b_1942_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1956_ = _args[0];
lean_object* v_lams_1957_ = _args[1];
lean_object* v_as_1958_ = _args[2];
lean_object* v_as_x27_1959_ = _args[3];
lean_object* v_b_1960_ = _args[4];
lean_object* v_a_1961_ = _args[5];
lean_object* v___y_1962_ = _args[6];
lean_object* v___y_1963_ = _args[7];
lean_object* v___y_1964_ = _args[8];
lean_object* v___y_1965_ = _args[9];
lean_object* v___y_1966_ = _args[10];
lean_object* v___y_1967_ = _args[11];
lean_object* v___y_1968_ = _args[12];
lean_object* v___y_1969_ = _args[13];
lean_object* v___y_1970_ = _args[14];
lean_object* v___y_1971_ = _args[15];
lean_object* v___y_1972_ = _args[16];
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1956_, v_lams_1957_, v_as_1958_, v_as_x27_1959_, v_b_1960_, v_a_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec(v_as_x27_1959_);
lean_dec(v_as_1958_);
lean_dec_ref(v_lams_1957_);
lean_dec_ref(v_a_1956_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1977_, lean_object* v_as_1978_, size_t v_sz_1979_, size_t v_i_1980_, lean_object* v_b_1981_){
_start:
{
lean_object* v_a_1983_; uint8_t v___x_1987_; 
v___x_1987_ = lean_usize_dec_lt(v_i_1980_, v_sz_1979_);
if (v___x_1987_ == 0)
{
lean_inc_ref(v_b_1981_);
return v_b_1981_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_a_1990_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1990_ = lean_array_uget_borrowed(v_as_1978_, v_i_1980_);
if (lean_obj_tag(v_a_1990_) == 6)
{
lean_object* v_binderType_1991_; size_t v___x_1992_; size_t v___x_1993_; uint8_t v___x_1994_; 
v_binderType_1991_ = lean_ctor_get(v_a_1990_, 1);
v___x_1992_ = lean_ptr_addr(v_d_1977_);
v___x_1993_ = lean_ptr_addr(v_binderType_1991_);
v___x_1994_ = lean_usize_dec_eq(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
v_a_1983_ = v___x_1989_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_inc_ref(v_a_1990_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_a_1990_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1988_);
return v___x_1997_;
}
}
else
{
v_a_1983_ = v___x_1989_;
goto v___jp_1982_;
}
}
v___jp_1982_:
{
size_t v___x_1984_; size_t v___x_1985_; 
v___x_1984_ = ((size_t)1ULL);
v___x_1985_ = lean_usize_add(v_i_1980_, v___x_1984_);
v_i_1980_ = v___x_1985_;
v_b_1981_ = v_a_1983_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1998_, lean_object* v_as_1999_, lean_object* v_sz_2000_, lean_object* v_i_2001_, lean_object* v_b_2002_){
_start:
{
size_t v_sz_boxed_2003_; size_t v_i_boxed_2004_; lean_object* v_res_2005_; 
v_sz_boxed_2003_ = lean_unbox_usize(v_sz_2000_);
lean_dec(v_sz_2000_);
v_i_boxed_2004_ = lean_unbox_usize(v_i_2001_);
lean_dec(v_i_2001_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1998_, v_as_1999_, v_sz_boxed_2003_, v_i_boxed_2004_, v_b_2002_);
lean_dec_ref(v_b_2002_);
lean_dec_ref(v_as_1999_);
lean_dec_ref(v_d_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2006_, lean_object* v_d_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; size_t v_sz_2010_; size_t v___x_2011_; lean_object* v___x_2012_; lean_object* v_fst_2013_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2010_ = lean_array_size(v_lams_2006_);
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2007_, v_lams_2006_, v_sz_2010_, v___x_2011_, v___x_2009_);
v_fst_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_fst_2013_);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v_fst_2013_) == 0)
{
return v___x_2008_;
}
else
{
lean_object* v_val_2014_; 
v_val_2014_ = lean_ctor_get(v_fst_2013_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v_fst_2013_, 1);
return v_val_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2015_, lean_object* v_d_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2015_, v_d_2016_);
lean_dec_ref(v_d_2016_);
lean_dec_ref(v_lams_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2028_, lean_object* v_as_2029_, size_t v_sz_2030_, size_t v_i_2031_, lean_object* v_b_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
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
lean_object* v_binderType_2053_; lean_object* v_body_2054_; lean_object* v___x_2055_; 
v_binderType_2053_ = lean_ctor_get(v_a_2052_, 1);
v_body_2054_ = lean_ctor_get(v_a_2052_, 2);
lean_inc_ref(v_binderType_2053_);
v___x_2055_ = l_Lean_Meta_getLevel(v_binderType_2053_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2058_ = lean_box(0);
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_a_2056_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
lean_inc_ref(v___x_2059_);
v___x_2060_ = l_Lean_mkConst(v___x_2057_, v___x_2059_);
lean_inc_ref(v_binderType_2053_);
v___x_2061_ = l_Lean_Expr_app___override(v___x_2060_, v_binderType_2053_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_Lean_Meta_synthInstance_x3f(v___x_2061_, v___x_2062_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
if (lean_obj_tag(v_a_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___x_2128_; 
v_val_2065_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v_a_2064_, 1);
v___x_2128_ = l_Lean_Expr_hasLooseBVars(v_body_2054_);
if (v___x_2128_ == 0)
{
v___y_2067_ = v___y_2033_;
v___y_2068_ = v___y_2034_;
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2059_);
v___x_2130_ = l_Lean_mkConst(v___x_2129_, v___x_2059_);
lean_inc_ref(v_binderType_2053_);
v___x_2131_ = l_Lean_Expr_app___override(v___x_2130_, v_binderType_2053_);
v___x_2132_ = l_Lean_Meta_synthInstance_x3f(v___x_2131_, v___x_2062_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
if (lean_obj_tag(v_a_2133_) == 0)
{
lean_dec(v_val_2065_);
lean_dec_ref_known(v___x_2059_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
else
{
lean_dec_ref_known(v_a_2133_, 1);
v___y_2067_ = v___y_2033_;
v___y_2068_ = v___y_2034_;
v___y_2069_ = v___y_2035_;
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
goto v___jp_2066_;
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_val_2065_);
lean_dec_ref_known(v___x_2059_, 2);
v_a_2134_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2132_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2132_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
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
v___jp_2066_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2028_, v_binderType_2053_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; 
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 1);
if (lean_obj_tag(v_val_2078_) == 6)
{
lean_object* v_body_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_body_2079_ = lean_ctor_get(v_val_2078_, 2);
v___x_2080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2081_ = l_Lean_mkConst(v___x_2080_, v___x_2059_);
lean_inc_ref(v_binderType_2053_);
v___x_2082_ = l_Lean_mkAppB(v___x_2081_, v_binderType_2053_, v_val_2065_);
v___x_2083_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2082_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = lean_expr_instantiate1(v_body_2054_, v_a_2084_);
v___x_2086_ = lean_expr_instantiate1(v_body_2079_, v_a_2084_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v_a_2052_);
v___x_2087_ = lean_grind_mk_eq_proof(v_a_2052_, v_val_2078_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Meta_mkCongrFun(v_a_2088_, v_a_2084_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Meta_mkEq(v___x_2085_, v___x_2086_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_mkExpectedPropHint(v_a_2090_, v_a_2092_);
v___x_2094_ = lean_unsigned_to_nat(0u);
v___x_2095_ = l_Lean_Meta_Grind_pushNewFact(v___x_2093_, v___x_2094_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
else
{
return v___x_2095_;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2090_);
v_a_2096_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2091_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2091_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2085_);
v_a_2104_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2089_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2089_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v___x_2086_);
lean_dec_ref(v___x_2085_);
lean_dec(v_a_2084_);
v_a_2112_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2087_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2087_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref_known(v_val_2078_, 3);
v_a_2120_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2083_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2083_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_val_2078_);
lean_dec(v_val_2065_);
lean_dec_ref_known(v___x_2059_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
else
{
lean_dec(v___x_2077_);
lean_dec(v_val_2065_);
lean_dec_ref_known(v___x_2059_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
}
else
{
lean_dec(v_a_2064_);
lean_dec_ref_known(v___x_2059_, 2);
v_a_2045_ = v___x_2051_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref_known(v___x_2059_, 2);
v_a_2142_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2063_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2063_);
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
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2055_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2055_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object* v_lams_u2082_2158_, lean_object* v_as_2159_, lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
size_t v_sz_boxed_2174_; size_t v_i_boxed_2175_; lean_object* v_res_2176_; 
v_sz_boxed_2174_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2175_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2158_, v_as_2159_, v_sz_boxed_2174_, v_i_boxed_2175_, v_b_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v_as_2159_);
lean_dec_ref(v_lams_u2082_2158_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2177_, lean_object* v_lams_u2082_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_array_get_size(v_lams_u2081_2177_);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_nat_dec_eq(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = lean_array_get_size(v_lams_u2082_2178_);
v___x_2197_ = lean_nat_dec_eq(v___x_2196_, v___x_2194_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_box(0);
v_sz_2199_ = lean_array_size(v_lams_u2081_2177_);
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2178_, v_lams_u2081_2177_, v_sz_2199_, v___x_2200_, v___x_2198_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v___x_2201_, 0);
lean_dec(v_unused_2209_);
v___x_2203_ = v___x_2201_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v___x_2201_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2198_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2198_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
return v___x_2201_;
}
}
else
{
goto v___jp_2190_;
}
}
else
{
goto v___jp_2190_;
}
v___jp_2190_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2210_, lean_object* v_lams_u2082_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2210_, v_lams_u2082_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_lams_u2082_2211_);
lean_dec_ref(v_lams_u2081_2210_);
return v_res_2223_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2226_){
_start:
{
uint8_t v_res_2227_; lean_object* v_r_2228_; 
v_res_2227_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2226_);
lean_dec_ref(v_x_2226_);
v_r_2228_ = lean_box(v_res_2227_);
return v_r_2228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2229_, lean_object* v_x_2230_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2232_, lean_object* v_x_2233_){
_start:
{
uint8_t v_res_2234_; lean_object* v_r_2235_; 
v_res_2234_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2232_, v_x_2233_);
lean_dec_ref(v_x_2233_);
v_r_2235_ = lean_box(v_res_2234_);
return v_r_2235_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2236_, lean_object* v_v_2237_, lean_object* v_i_2238_){
_start:
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_array_get_size(v_xs_2236_);
v___x_2240_ = lean_nat_dec_lt(v_i_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
lean_dec(v_i_2238_);
v___x_2241_ = lean_box(0);
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; size_t v___x_2243_; size_t v___x_2244_; uint8_t v___x_2245_; 
v___x_2242_ = lean_array_fget_borrowed(v_xs_2236_, v_i_2238_);
v___x_2243_ = lean_ptr_addr(v___x_2242_);
v___x_2244_ = lean_ptr_addr(v_v_2237_);
v___x_2245_ = lean_usize_dec_eq(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_add(v_i_2238_, v___x_2246_);
lean_dec(v_i_2238_);
v_i_2238_ = v___x_2247_;
goto _start;
}
else
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_i_2238_);
return v___x_2249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2250_, lean_object* v_v_2251_, lean_object* v_i_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2250_, v_v_2251_, v_i_2252_);
lean_dec_ref(v_v_2251_);
lean_dec_ref(v_xs_2250_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2254_, lean_object* v_v_2255_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2254_, v_v_2255_, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2258_, lean_object* v_v_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2258_, v_v_2259_);
lean_dec_ref(v_v_2259_);
lean_dec_ref(v_xs_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2261_, size_t v_x_2262_, lean_object* v_x_2263_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 0)
{
lean_object* v_es_2264_; lean_object* v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v_j_2268_; lean_object* v_entry_2269_; 
v_es_2264_ = lean_ctor_get(v_x_2261_, 0);
v___x_2265_ = lean_box(2);
v___x_2266_ = ((size_t)31ULL);
v___x_2267_ = lean_usize_land(v_x_2262_, v___x_2266_);
v_j_2268_ = lean_usize_to_nat(v___x_2267_);
v_entry_2269_ = lean_array_get(v___x_2265_, v_es_2264_, v_j_2268_);
switch(lean_obj_tag(v_entry_2269_))
{
case 0:
{
lean_object* v_key_2270_; size_t v___x_2271_; size_t v___x_2272_; uint8_t v___x_2273_; 
v_key_2270_ = lean_ctor_get(v_entry_2269_, 0);
lean_inc(v_key_2270_);
lean_dec_ref_known(v_entry_2269_, 2);
v___x_2271_ = lean_ptr_addr(v_x_2263_);
v___x_2272_ = lean_ptr_addr(v_key_2270_);
lean_dec(v_key_2270_);
v___x_2273_ = lean_usize_dec_eq(v___x_2271_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec(v_j_2268_);
return v_x_2261_;
}
else
{
lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
lean_inc_ref(v_es_2264_);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_x_2261_, 0);
lean_dec(v_unused_2282_);
v___x_2275_ = v_x_2261_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_dec(v_x_2261_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_array_set(v_es_2264_, v_j_2268_, v___x_2265_);
lean_dec(v_j_2268_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
case 1:
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2317_; 
lean_inc_ref(v_es_2264_);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v_x_2261_, 0);
lean_dec(v_unused_2318_);
v___x_2284_ = v_x_2261_;
v_isShared_2285_ = v_isSharedCheck_2317_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_x_2261_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2317_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_node_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2316_; 
v_node_2286_ = lean_ctor_get(v_entry_2269_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_entry_2269_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2288_ = v_entry_2269_;
v_isShared_2289_ = v_isSharedCheck_2316_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_node_2286_);
lean_dec(v_entry_2269_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2316_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
size_t v___x_2290_; lean_object* v_entries_2291_; size_t v___x_2292_; lean_object* v_newNode_2293_; lean_object* v___x_2294_; 
v___x_2290_ = ((size_t)5ULL);
v_entries_2291_ = lean_array_set(v_es_2264_, v_j_2268_, v___x_2265_);
v___x_2292_ = lean_usize_shift_right(v_x_2262_, v___x_2290_);
v_newNode_2293_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2286_, v___x_2292_, v_x_2263_);
lean_inc_ref(v_newNode_2293_);
v___x_2294_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2296_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v_newNode_2293_);
v___x_2296_ = v___x_2288_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_newNode_2293_);
v___x_2296_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_array_set(v_entries_2291_, v_j_2268_, v___x_2296_);
lean_dec(v_j_2268_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2297_);
v___x_2299_ = v___x_2284_;
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
lean_object* v_val_2302_; lean_object* v_fst_2303_; lean_object* v_snd_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_newNode_2293_);
lean_del_object(v___x_2288_);
v_val_2302_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v___x_2294_, 1);
v_fst_2303_ = lean_ctor_get(v_val_2302_, 0);
v_snd_2304_ = lean_ctor_get(v_val_2302_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_val_2302_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2306_ = v_val_2302_;
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2304_);
lean_inc(v_fst_2303_);
lean_dec(v_val_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_fst_2303_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_snd_2304_);
v___x_2309_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_array_set(v_entries_2291_, v_j_2268_, v___x_2309_);
lean_dec(v_j_2268_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2310_);
v___x_2312_ = v___x_2284_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2268_);
return v_x_2261_;
}
}
}
else
{
lean_object* v_ks_2319_; lean_object* v_vs_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2334_; 
v_ks_2319_ = lean_ctor_get(v_x_2261_, 0);
v_vs_2320_ = lean_ctor_get(v_x_2261_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2261_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2322_ = v_x_2261_;
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_vs_2320_);
lean_inc(v_ks_2319_);
lean_dec(v_x_2261_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2319_, v_x_2263_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2326_; 
if (v_isShared_2323_ == 0)
{
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_ks_2319_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_vs_2320_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
lean_object* v_val_2328_; lean_object* v_keys_x27_2329_; lean_object* v_vals_x27_2330_; lean_object* v___x_2332_; 
v_val_2328_ = lean_ctor_get(v___x_2324_, 0);
lean_inc_n(v_val_2328_, 2);
lean_dec_ref_known(v___x_2324_, 1);
v_keys_x27_2329_ = l_Array_eraseIdx___redArg(v_ks_2319_, v_val_2328_);
v_vals_x27_2330_ = l_Array_eraseIdx___redArg(v_vs_2320_, v_val_2328_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v_vals_x27_2330_);
lean_ctor_set(v___x_2322_, 0, v_keys_x27_2329_);
v___x_2332_ = v___x_2322_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_keys_x27_2329_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_vals_x27_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
size_t v_x_19541__boxed_2338_; lean_object* v_res_2339_; 
v_x_19541__boxed_2338_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_res_2339_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2335_, v_x_19541__boxed_2338_, v_x_2337_);
lean_dec_ref(v_x_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
size_t v___x_2342_; size_t v___x_2343_; size_t v___x_2344_; uint64_t v___x_2345_; size_t v_h_2346_; lean_object* v___x_2347_; 
v___x_2342_ = lean_ptr_addr(v_x_2341_);
v___x_2343_ = ((size_t)3ULL);
v___x_2344_ = lean_usize_shift_right(v___x_2342_, v___x_2343_);
v___x_2345_ = lean_usize_to_uint64(v___x_2344_);
v_h_2346_ = lean_uint64_to_usize(v___x_2345_);
v___x_2347_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2340_, v_h_2346_, v_x_2341_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2348_, v_x_2349_);
lean_dec_ref(v_x_2349_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
if (lean_obj_tag(v_as_2351_) == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_head_2365_; lean_object* v_tail_2366_; lean_object* v___x_2367_; 
v_head_2365_ = lean_ctor_get(v_as_2351_, 0);
lean_inc(v_head_2365_);
v_tail_2366_ = lean_ctor_get(v_as_2351_, 1);
lean_inc(v_tail_2366_);
lean_dec_ref_known(v_as_2351_, 2);
v___x_2367_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2365_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
v_as_2351_ = v_tail_2366_;
goto _start;
}
else
{
lean_dec(v_tail_2366_);
return v___x_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2382_, lean_object* v_vals_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
_start:
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = lean_array_get_size(v_keys_2382_);
v___x_2387_ = lean_nat_dec_lt(v_i_2384_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
lean_dec(v_i_2384_);
v___x_2388_ = lean_box(0);
return v___x_2388_;
}
else
{
lean_object* v_k_x27_2389_; size_t v___x_2390_; size_t v___x_2391_; uint8_t v___x_2392_; 
v_k_x27_2389_ = lean_array_fget_borrowed(v_keys_2382_, v_i_2384_);
v___x_2390_ = lean_ptr_addr(v_k_2385_);
v___x_2391_ = lean_ptr_addr(v_k_x27_2389_);
v___x_2392_ = lean_usize_dec_eq(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_nat_add(v_i_2384_, v___x_2393_);
lean_dec(v_i_2384_);
v_i_2384_ = v___x_2394_;
goto _start;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_array_fget_borrowed(v_vals_2383_, v_i_2384_);
lean_dec(v_i_2384_);
lean_inc(v___x_2396_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2398_, lean_object* v_vals_2399_, lean_object* v_i_2400_, lean_object* v_k_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2398_, v_vals_2399_, v_i_2400_, v_k_2401_);
lean_dec_ref(v_k_2401_);
lean_dec_ref(v_vals_2399_);
lean_dec_ref(v_keys_2398_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2403_, size_t v_x_2404_, lean_object* v_x_2405_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 0)
{
lean_object* v_es_2406_; lean_object* v___x_2407_; size_t v___x_2408_; size_t v___x_2409_; lean_object* v_j_2410_; lean_object* v___x_2411_; 
v_es_2406_ = lean_ctor_get(v_x_2403_, 0);
v___x_2407_ = lean_box(2);
v___x_2408_ = ((size_t)31ULL);
v___x_2409_ = lean_usize_land(v_x_2404_, v___x_2408_);
v_j_2410_ = lean_usize_to_nat(v___x_2409_);
v___x_2411_ = lean_array_get_borrowed(v___x_2407_, v_es_2406_, v_j_2410_);
lean_dec(v_j_2410_);
switch(lean_obj_tag(v___x_2411_))
{
case 0:
{
lean_object* v_key_2412_; lean_object* v_val_2413_; size_t v___x_2414_; size_t v___x_2415_; uint8_t v___x_2416_; 
v_key_2412_ = lean_ctor_get(v___x_2411_, 0);
v_val_2413_ = lean_ctor_get(v___x_2411_, 1);
v___x_2414_ = lean_ptr_addr(v_x_2405_);
v___x_2415_ = lean_ptr_addr(v_key_2412_);
v___x_2416_ = lean_usize_dec_eq(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_box(0);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; 
lean_inc(v_val_2413_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_val_2413_);
return v___x_2418_;
}
}
case 1:
{
lean_object* v_node_2419_; size_t v___x_2420_; size_t v___x_2421_; 
v_node_2419_ = lean_ctor_get(v___x_2411_, 0);
v___x_2420_ = ((size_t)5ULL);
v___x_2421_ = lean_usize_shift_right(v_x_2404_, v___x_2420_);
v_x_2403_ = v_node_2419_;
v_x_2404_ = v___x_2421_;
goto _start;
}
default: 
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_box(0);
return v___x_2423_;
}
}
}
else
{
lean_object* v_ks_2424_; lean_object* v_vs_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_ks_2424_ = lean_ctor_get(v_x_2403_, 0);
v_vs_2425_ = lean_ctor_get(v_x_2403_, 1);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2424_, v_vs_2425_, v___x_2426_, v_x_2405_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
size_t v_x_19766__boxed_2431_; lean_object* v_res_2432_; 
v_x_19766__boxed_2431_ = lean_unbox_usize(v_x_2429_);
lean_dec(v_x_2429_);
v_res_2432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2428_, v_x_19766__boxed_2431_, v_x_2430_);
lean_dec_ref(v_x_2430_);
lean_dec_ref(v_x_2428_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
size_t v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; uint64_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2435_ = lean_ptr_addr(v_x_2434_);
v___x_2436_ = ((size_t)3ULL);
v___x_2437_ = lean_usize_shift_right(v___x_2435_, v___x_2436_);
v___x_2438_ = lean_usize_to_uint64(v___x_2437_);
v___x_2439_ = lean_uint64_to_usize(v___x_2438_);
v___x_2440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2433_, v___x_2439_, v_x_2434_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2441_, v_x_2442_);
lean_dec_ref(v_x_2442_);
lean_dec_ref(v_x_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2444_, lean_object* v_b_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
if (lean_obj_tag(v_as_x27_2444_) == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_b_2445_);
return v___x_2457_;
}
else
{
lean_object* v_head_2458_; lean_object* v_tail_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_toGoalState_2462_; lean_object* v_ematch_2463_; lean_object* v_delayedThmInsts_2464_; lean_object* v___x_2465_; 
v_head_2458_ = lean_ctor_get(v_as_x27_2444_, 0);
v_tail_2459_ = lean_ctor_get(v_as_x27_2444_, 1);
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_st_ref_get(v___y_2446_);
v_toGoalState_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc_ref(v_toGoalState_2462_);
lean_dec(v___x_2461_);
v_ematch_2463_ = lean_ctor_get(v_toGoalState_2462_, 13);
lean_inc_ref(v_ematch_2463_);
lean_dec_ref(v_toGoalState_2462_);
v_delayedThmInsts_2464_ = lean_ctor_get(v_ematch_2463_, 10);
lean_inc_ref(v_delayedThmInsts_2464_);
lean_dec_ref(v_ematch_2463_);
v___x_2465_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2464_, v_head_2458_);
lean_dec_ref(v_delayedThmInsts_2464_);
if (lean_obj_tag(v___x_2465_) == 1)
{
lean_object* v_val_2466_; lean_object* v___x_2467_; lean_object* v_toGoalState_2468_; lean_object* v_ematch_2469_; lean_object* v_mvarId_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2526_; 
v_val_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_st_ref_take(v___y_2446_);
v_toGoalState_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_toGoalState_2468_);
v_ematch_2469_ = lean_ctor_get(v_toGoalState_2468_, 13);
lean_inc_ref(v_ematch_2469_);
v_mvarId_2470_ = lean_ctor_get(v___x_2467_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2467_, 0);
lean_dec(v_unused_2527_);
v___x_2472_ = v___x_2467_;
v_isShared_2473_ = v_isSharedCheck_2526_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_mvarId_2470_);
lean_dec(v___x_2467_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2526_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_nextDeclIdx_2474_; lean_object* v_enodeMap_2475_; lean_object* v_exprs_2476_; lean_object* v_parents_2477_; lean_object* v_congrTable_2478_; lean_object* v_appMap_2479_; lean_object* v_indicesFound_2480_; lean_object* v_toProcess_2481_; lean_object* v_internalizing_2482_; uint8_t v_inconsistent_2483_; lean_object* v_nextIdx_2484_; lean_object* v_newRawFacts_2485_; lean_object* v_facts_2486_; lean_object* v_extThms_2487_; lean_object* v_inj_2488_; lean_object* v_split_2489_; lean_object* v_clean_2490_; lean_object* v_sstates_2491_; lean_object* v_goalStack_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2524_; 
v_nextDeclIdx_2474_ = lean_ctor_get(v_toGoalState_2468_, 0);
v_enodeMap_2475_ = lean_ctor_get(v_toGoalState_2468_, 1);
v_exprs_2476_ = lean_ctor_get(v_toGoalState_2468_, 2);
v_parents_2477_ = lean_ctor_get(v_toGoalState_2468_, 3);
v_congrTable_2478_ = lean_ctor_get(v_toGoalState_2468_, 4);
v_appMap_2479_ = lean_ctor_get(v_toGoalState_2468_, 5);
v_indicesFound_2480_ = lean_ctor_get(v_toGoalState_2468_, 6);
v_toProcess_2481_ = lean_ctor_get(v_toGoalState_2468_, 7);
v_internalizing_2482_ = lean_ctor_get(v_toGoalState_2468_, 8);
v_inconsistent_2483_ = lean_ctor_get_uint8(v_toGoalState_2468_, sizeof(void*)*19);
v_nextIdx_2484_ = lean_ctor_get(v_toGoalState_2468_, 9);
v_newRawFacts_2485_ = lean_ctor_get(v_toGoalState_2468_, 10);
v_facts_2486_ = lean_ctor_get(v_toGoalState_2468_, 11);
v_extThms_2487_ = lean_ctor_get(v_toGoalState_2468_, 12);
v_inj_2488_ = lean_ctor_get(v_toGoalState_2468_, 14);
v_split_2489_ = lean_ctor_get(v_toGoalState_2468_, 15);
v_clean_2490_ = lean_ctor_get(v_toGoalState_2468_, 16);
v_sstates_2491_ = lean_ctor_get(v_toGoalState_2468_, 17);
v_goalStack_2492_ = lean_ctor_get(v_toGoalState_2468_, 18);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_toGoalState_2468_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v_toGoalState_2468_, 13);
lean_dec(v_unused_2525_);
v___x_2494_ = v_toGoalState_2468_;
v_isShared_2495_ = v_isSharedCheck_2524_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_goalStack_2492_);
lean_inc(v_sstates_2491_);
lean_inc(v_clean_2490_);
lean_inc(v_split_2489_);
lean_inc(v_inj_2488_);
lean_inc(v_extThms_2487_);
lean_inc(v_facts_2486_);
lean_inc(v_newRawFacts_2485_);
lean_inc(v_nextIdx_2484_);
lean_inc(v_internalizing_2482_);
lean_inc(v_toProcess_2481_);
lean_inc(v_indicesFound_2480_);
lean_inc(v_appMap_2479_);
lean_inc(v_congrTable_2478_);
lean_inc(v_parents_2477_);
lean_inc(v_exprs_2476_);
lean_inc(v_enodeMap_2475_);
lean_inc(v_nextDeclIdx_2474_);
lean_dec(v_toGoalState_2468_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2524_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_thmMap_2496_; lean_object* v_gmt_2497_; lean_object* v_thms_2498_; lean_object* v_newThms_2499_; lean_object* v_numInstances_2500_; lean_object* v_numDelayedInstances_2501_; lean_object* v_num_2502_; lean_object* v_preInstances_2503_; lean_object* v_nextThmIdx_2504_; lean_object* v_matchEqNames_2505_; lean_object* v_delayedThmInsts_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2523_; 
v_thmMap_2496_ = lean_ctor_get(v_ematch_2469_, 0);
v_gmt_2497_ = lean_ctor_get(v_ematch_2469_, 1);
v_thms_2498_ = lean_ctor_get(v_ematch_2469_, 2);
v_newThms_2499_ = lean_ctor_get(v_ematch_2469_, 3);
v_numInstances_2500_ = lean_ctor_get(v_ematch_2469_, 4);
v_numDelayedInstances_2501_ = lean_ctor_get(v_ematch_2469_, 5);
v_num_2502_ = lean_ctor_get(v_ematch_2469_, 6);
v_preInstances_2503_ = lean_ctor_get(v_ematch_2469_, 7);
v_nextThmIdx_2504_ = lean_ctor_get(v_ematch_2469_, 8);
v_matchEqNames_2505_ = lean_ctor_get(v_ematch_2469_, 9);
v_delayedThmInsts_2506_ = lean_ctor_get(v_ematch_2469_, 10);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_ematch_2469_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2508_ = v_ematch_2469_;
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_delayedThmInsts_2506_);
lean_inc(v_matchEqNames_2505_);
lean_inc(v_nextThmIdx_2504_);
lean_inc(v_preInstances_2503_);
lean_inc(v_num_2502_);
lean_inc(v_numDelayedInstances_2501_);
lean_inc(v_numInstances_2500_);
lean_inc(v_newThms_2499_);
lean_inc(v_thms_2498_);
lean_inc(v_gmt_2497_);
lean_inc(v_thmMap_2496_);
lean_dec(v_ematch_2469_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2506_, v_head_2458_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 10, v___x_2510_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_thmMap_2496_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_gmt_2497_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_thms_2498_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_newThms_2499_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_numInstances_2500_);
lean_ctor_set(v_reuseFailAlloc_2522_, 5, v_numDelayedInstances_2501_);
lean_ctor_set(v_reuseFailAlloc_2522_, 6, v_num_2502_);
lean_ctor_set(v_reuseFailAlloc_2522_, 7, v_preInstances_2503_);
lean_ctor_set(v_reuseFailAlloc_2522_, 8, v_nextThmIdx_2504_);
lean_ctor_set(v_reuseFailAlloc_2522_, 9, v_matchEqNames_2505_);
lean_ctor_set(v_reuseFailAlloc_2522_, 10, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 13, v___x_2512_);
v___x_2514_ = v___x_2494_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_nextDeclIdx_2474_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_enodeMap_2475_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_exprs_2476_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_parents_2477_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_congrTable_2478_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_appMap_2479_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_indicesFound_2480_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_toProcess_2481_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_internalizing_2482_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_nextIdx_2484_);
lean_ctor_set(v_reuseFailAlloc_2521_, 10, v_newRawFacts_2485_);
lean_ctor_set(v_reuseFailAlloc_2521_, 11, v_facts_2486_);
lean_ctor_set(v_reuseFailAlloc_2521_, 12, v_extThms_2487_);
lean_ctor_set(v_reuseFailAlloc_2521_, 13, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2521_, 14, v_inj_2488_);
lean_ctor_set(v_reuseFailAlloc_2521_, 15, v_split_2489_);
lean_ctor_set(v_reuseFailAlloc_2521_, 16, v_clean_2490_);
lean_ctor_set(v_reuseFailAlloc_2521_, 17, v_sstates_2491_);
lean_ctor_set(v_reuseFailAlloc_2521_, 18, v_goalStack_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2521_, sizeof(void*)*19, v_inconsistent_2483_);
v___x_2514_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2514_);
v___x_2516_ = v___x_2472_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_mvarId_2470_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_st_ref_put(v___y_2446_, v___x_2516_);
v___x_2518_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2466_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_dec_ref_known(v___x_2518_, 1);
v_as_x27_2444_ = v_tail_2459_;
v_b_2445_ = v___x_2460_;
goto _start;
}
else
{
return v___x_2518_;
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
lean_dec(v___x_2465_);
v_as_x27_2444_ = v_tail_2459_;
v_b_2445_ = v___x_2460_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2529_, v_b_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v_as_x27_2529_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2544_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2584_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v_toGoalState_2562_; lean_object* v_ematch_2563_; lean_object* v_delayedThmInsts_2564_; uint8_t v___x_2565_; 
v___x_2561_ = lean_st_ref_get(v_a_2544_);
v_toGoalState_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_toGoalState_2562_);
lean_dec(v___x_2561_);
v_ematch_2563_ = lean_ctor_get(v_toGoalState_2562_, 13);
lean_inc_ref(v_ematch_2563_);
lean_dec_ref(v_toGoalState_2562_);
v_delayedThmInsts_2564_ = lean_ctor_get(v_ematch_2563_, 10);
lean_inc_ref(v_delayedThmInsts_2564_);
lean_dec_ref(v_ematch_2563_);
v___x_2565_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2564_);
lean_dec_ref(v_delayedThmInsts_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_del_object(v___x_2558_);
v___x_2566_ = lean_box(0);
v___x_2567_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2543_, v___x_2566_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2575_);
v___x_2569_ = v___x_2567_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2567_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2566_);
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2566_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2576_);
v___x_2578_ = v___x_2558_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2580_);
v___x_2582_ = v___x_2558_;
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
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2555_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2555_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec(v_toPropagateDown_2593_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2607_, v_x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2610_, v_x_2611_, v_x_2612_);
lean_dec_ref(v_x_2612_);
lean_dec_ref(v_x_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2618_, v_x_2619_, v_x_2620_);
lean_dec_ref(v_x_2620_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2622_, lean_object* v_as_x27_2623_, lean_object* v_b_2624_, lean_object* v_a_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2623_, v_b_2624_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2638_, lean_object* v_as_x27_2639_, lean_object* v_b_2640_, lean_object* v_a_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2638_, v_as_x27_2639_, v_b_2640_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v_as_x27_2639_);
lean_dec(v_as_2638_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2654_, lean_object* v_x_2655_, size_t v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2655_, v_x_2656_, v_x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
size_t v_x_20071__boxed_2663_; lean_object* v_res_2664_; 
v_x_20071__boxed_2663_ = lean_unbox_usize(v_x_2661_);
lean_dec(v_x_2661_);
v_res_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2659_, v_x_2660_, v_x_20071__boxed_2663_, v_x_2662_);
lean_dec_ref(v_x_2662_);
lean_dec_ref(v_x_2660_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, size_t v_x_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2666_, v_x_2667_, v_x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
size_t v_x_20082__boxed_2674_; lean_object* v_res_2675_; 
v_x_20082__boxed_2674_ = lean_unbox_usize(v_x_2672_);
lean_dec(v_x_2672_);
v_res_2675_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2670_, v_x_2671_, v_x_20082__boxed_2674_, v_x_2673_);
lean_dec_ref(v_x_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2676_, lean_object* v_keys_2677_, lean_object* v_vals_2678_, lean_object* v_heq_2679_, lean_object* v_i_2680_, lean_object* v_k_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2677_, v_vals_2678_, v_i_2680_, v_k_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2683_, lean_object* v_keys_2684_, lean_object* v_vals_2685_, lean_object* v_heq_2686_, lean_object* v_i_2687_, lean_object* v_k_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2683_, v_keys_2684_, v_vals_2685_, v_heq_2686_, v_i_2687_, v_k_2688_);
lean_dec_ref(v_k_2688_);
lean_dec_ref(v_vals_2685_);
lean_dec_ref(v_keys_2684_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2690_, lean_object* v_keys_2691_, lean_object* v_vals_2692_, lean_object* v_i_2693_, lean_object* v_k_2694_){
_start:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = lean_array_get_size(v_keys_2691_);
v___x_2696_ = lean_nat_dec_lt(v_i_2693_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; 
lean_dec_ref(v_k_2694_);
lean_dec(v_i_2693_);
v___x_2697_ = lean_box(0);
return v___x_2697_;
}
else
{
lean_object* v_k_x27_2698_; uint8_t v___x_2699_; 
v_k_x27_2698_ = lean_array_fget_borrowed(v_keys_2691_, v_i_2693_);
lean_inc(v_k_x27_2698_);
lean_inc_ref(v_k_2694_);
v___x_2699_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2690_, v_k_2694_, v_k_x27_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_add(v_i_2693_, v___x_2700_);
lean_dec(v_i_2693_);
v_i_2693_ = v___x_2701_;
goto _start;
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v_k_2694_);
v___x_2703_ = lean_array_fget_borrowed(v_vals_2692_, v_i_2693_);
lean_dec(v_i_2693_);
lean_inc(v___x_2703_);
lean_inc(v_k_x27_2698_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_k_x27_2698_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2706_, lean_object* v_keys_2707_, lean_object* v_vals_2708_, lean_object* v_i_2709_, lean_object* v_k_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2706_, v_keys_2707_, v_vals_2708_, v_i_2709_, v_k_2710_);
lean_dec_ref(v_vals_2708_);
lean_dec_ref(v_keys_2707_);
lean_dec_ref(v___x_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2712_, lean_object* v_x_2713_, size_t v_x_2714_, lean_object* v_x_2715_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
lean_object* v_es_2716_; lean_object* v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; lean_object* v_j_2720_; lean_object* v___x_2721_; 
v_es_2716_ = lean_ctor_get(v_x_2713_, 0);
lean_inc_ref(v_es_2716_);
lean_dec_ref_known(v_x_2713_, 1);
v___x_2717_ = lean_box(2);
v___x_2718_ = ((size_t)31ULL);
v___x_2719_ = lean_usize_land(v_x_2714_, v___x_2718_);
v_j_2720_ = lean_usize_to_nat(v___x_2719_);
v___x_2721_ = lean_array_get(v___x_2717_, v_es_2716_, v_j_2720_);
lean_dec(v_j_2720_);
lean_dec_ref(v_es_2716_);
switch(lean_obj_tag(v___x_2721_))
{
case 0:
{
lean_object* v_key_2722_; lean_object* v_val_2723_; uint8_t v___x_2724_; 
v_key_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_n(v_key_2722_, 2);
v_val_2723_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_val_2723_);
lean_dec_ref_known(v___x_2721_, 2);
v___x_2724_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2712_, v_x_2715_, v_key_2722_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v_val_2723_);
lean_dec(v_key_2722_);
v___x_2725_ = lean_box(0);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_key_2722_);
lean_ctor_set(v___x_2726_, 1, v_val_2723_);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
}
case 1:
{
lean_object* v_node_2728_; size_t v___x_2729_; size_t v___x_2730_; 
v_node_2728_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_node_2728_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2729_ = ((size_t)5ULL);
v___x_2730_ = lean_usize_shift_right(v_x_2714_, v___x_2729_);
v_x_2713_ = v_node_2728_;
v_x_2714_ = v___x_2730_;
goto _start;
}
default: 
{
lean_object* v___x_2732_; 
lean_dec_ref(v_x_2715_);
v___x_2732_ = lean_box(0);
return v___x_2732_;
}
}
}
else
{
lean_object* v_ks_2733_; lean_object* v_vs_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_ks_2733_ = lean_ctor_get(v_x_2713_, 0);
lean_inc_ref(v_ks_2733_);
v_vs_2734_ = lean_ctor_get(v_x_2713_, 1);
lean_inc_ref(v_vs_2734_);
lean_dec_ref_known(v_x_2713_, 2);
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2712_, v_ks_2733_, v_vs_2734_, v___x_2735_, v_x_2715_);
lean_dec_ref(v_vs_2734_);
lean_dec_ref(v_ks_2733_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
size_t v_x_26255__boxed_2741_; lean_object* v_res_2742_; 
v_x_26255__boxed_2741_ = lean_unbox_usize(v_x_2739_);
lean_dec(v_x_2739_);
v_res_2742_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2737_, v_x_2738_, v_x_26255__boxed_2741_, v_x_2740_);
lean_dec_ref(v___x_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_){
_start:
{
uint64_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2743_, v_x_2745_);
v___x_2747_ = lean_uint64_to_usize(v___x_2746_);
lean_inc_ref(v_x_2744_);
v___x_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v___x_2747_, v_x_2745_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2749_, v_x_2750_, v_x_2751_);
lean_dec_ref(v_x_2750_);
lean_dec_ref(v___x_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_ks_2758_; lean_object* v_vs_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2783_; 
v_ks_2758_ = lean_ctor_get(v_x_2754_, 0);
v_vs_2759_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2761_ = v_x_2754_;
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_vs_2759_);
lean_inc(v_ks_2758_);
lean_dec(v_x_2754_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_array_get_size(v_ks_2758_);
v___x_2764_ = lean_nat_dec_lt(v_x_2755_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_x_2755_);
v___x_2765_ = lean_array_push(v_ks_2758_, v_x_2756_);
v___x_2766_ = lean_array_push(v_vs_2759_, v_x_2757_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2766_);
lean_ctor_set(v___x_2761_, 0, v___x_2765_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v_k_x27_2770_; uint8_t v___x_2771_; 
v_k_x27_2770_ = lean_array_fget_borrowed(v_ks_2758_, v_x_2755_);
lean_inc(v_k_x27_2770_);
lean_inc_ref(v_x_2756_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2753_, v_x_2756_, v_k_x27_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; 
if (v_isShared_2762_ == 0)
{
v___x_2773_ = v___x_2761_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_ks_2758_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_vs_2759_);
v___x_2773_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_add(v_x_2755_, v___x_2774_);
lean_dec(v_x_2755_);
v_x_2754_ = v___x_2773_;
v_x_2755_ = v___x_2775_;
goto _start;
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = lean_array_fset(v_ks_2758_, v_x_2755_, v_x_2756_);
v___x_2779_ = lean_array_fset(v_vs_2759_, v_x_2755_, v_x_2757_);
lean_dec(v_x_2755_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2779_);
lean_ctor_set(v___x_2761_, 0, v___x_2778_);
v___x_2781_ = v___x_2761_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2784_, v_x_2785_, v_x_2786_, v_x_2787_, v_x_2788_);
lean_dec_ref(v___x_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2790_, lean_object* v_n_2791_, lean_object* v_k_2792_, lean_object* v_v_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2790_, v_n_2791_, v___x_2794_, v_k_2792_, v_v_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2796_, lean_object* v_n_2797_, lean_object* v_k_2798_, lean_object* v_v_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2796_, v_n_2797_, v_k_2798_, v_v_2799_);
lean_dec_ref(v___x_2796_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2802_, lean_object* v_x_2803_, size_t v_x_2804_, size_t v_x_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v_es_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v_j_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_es_2808_ = lean_ctor_get(v_x_2803_, 0);
v___x_2809_ = ((size_t)31ULL);
v___x_2810_ = lean_usize_land(v_x_2804_, v___x_2809_);
v_j_2811_ = lean_usize_to_nat(v___x_2810_);
v___x_2812_ = lean_array_get_size(v_es_2808_);
v___x_2813_ = lean_nat_dec_lt(v_j_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_dec(v_j_2811_);
lean_dec(v_x_2807_);
lean_dec_ref(v_x_2806_);
return v_x_2803_;
}
else
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2852_; 
lean_inc_ref(v_es_2808_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_x_2803_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v_x_2803_, 0);
lean_dec(v_unused_2853_);
v___x_2815_ = v_x_2803_;
v_isShared_2816_ = v_isSharedCheck_2852_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_x_2803_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2852_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_v_2817_; lean_object* v___x_2818_; lean_object* v_xs_x27_2819_; lean_object* v___y_2821_; 
v_v_2817_ = lean_array_fget(v_es_2808_, v_j_2811_);
v___x_2818_ = lean_box(0);
v_xs_x27_2819_ = lean_array_fset(v_es_2808_, v_j_2811_, v___x_2818_);
switch(lean_obj_tag(v_v_2817_))
{
case 0:
{
lean_object* v_key_2826_; lean_object* v_val_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2837_; 
v_key_2826_ = lean_ctor_get(v_v_2817_, 0);
v_val_2827_ = lean_ctor_get(v_v_2817_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_v_2817_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2829_ = v_v_2817_;
v_isShared_2830_ = v_isSharedCheck_2837_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_val_2827_);
lean_inc(v_key_2826_);
lean_dec(v_v_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2837_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
uint8_t v___x_2831_; 
lean_inc(v_key_2826_);
lean_inc_ref(v_x_2806_);
v___x_2831_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2802_, v_x_2806_, v_key_2826_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2829_);
v___x_2832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2826_, v_val_2827_, v_x_2806_, v_x_2807_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
v___y_2821_ = v___x_2833_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2835_; 
lean_dec(v_val_2827_);
lean_dec(v_key_2826_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_x_2807_);
lean_ctor_set(v___x_2829_, 0, v_x_2806_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_x_2806_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_x_2807_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
v___y_2821_ = v___x_2835_;
goto v___jp_2820_;
}
}
}
}
case 1:
{
lean_object* v_node_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2850_; 
v_node_2838_ = lean_ctor_get(v_v_2817_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_v_2817_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2840_ = v_v_2817_;
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_node_2838_);
lean_dec(v_v_2817_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2842_ = ((size_t)5ULL);
v___x_2843_ = lean_usize_shift_right(v_x_2804_, v___x_2842_);
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_x_2805_, v___x_2844_);
v___x_2846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2802_, v_node_2838_, v___x_2843_, v___x_2845_, v_x_2806_, v_x_2807_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2846_);
v___x_2848_ = v___x_2840_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
v___y_2821_ = v___x_2848_;
goto v___jp_2820_;
}
}
}
default: 
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_x_2806_);
lean_ctor_set(v___x_2851_, 1, v_x_2807_);
v___y_2821_ = v___x_2851_;
goto v___jp_2820_;
}
}
v___jp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_array_fset(v_xs_x27_2819_, v_j_2811_, v___y_2821_);
lean_dec(v_j_2811_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2822_);
v___x_2824_ = v___x_2815_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_ks_2854_; lean_object* v_vs_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2873_; 
v_ks_2854_ = lean_ctor_get(v_x_2803_, 0);
v_vs_2855_ = lean_ctor_get(v_x_2803_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2803_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2857_ = v_x_2803_;
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_vs_2855_);
lean_inc(v_ks_2854_);
lean_dec(v_x_2803_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_ks_2854_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_vs_2855_);
v___x_2860_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v_newNode_2861_; size_t v___x_2862_; uint8_t v___x_2863_; 
v_newNode_2861_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2802_, v___x_2860_, v_x_2806_, v_x_2807_);
v___x_2862_ = ((size_t)7ULL);
v___x_2863_ = lean_usize_dec_le(v___x_2862_, v_x_2805_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2864_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2861_);
v___x_2865_ = lean_unsigned_to_nat(4u);
v___x_2866_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
lean_dec(v___x_2864_);
if (v___x_2866_ == 0)
{
lean_object* v_ks_2867_; lean_object* v_vs_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_ks_2867_ = lean_ctor_get(v_newNode_2861_, 0);
lean_inc_ref(v_ks_2867_);
v_vs_2868_ = lean_ctor_get(v_newNode_2861_, 1);
lean_inc_ref(v_vs_2868_);
lean_dec_ref(v_newNode_2861_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2802_, v_x_2805_, v_ks_2867_, v_vs_2868_, v___x_2869_, v___x_2870_);
lean_dec_ref(v_vs_2868_);
lean_dec_ref(v_ks_2867_);
return v___x_2871_;
}
else
{
return v_newNode_2861_;
}
}
else
{
return v_newNode_2861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2874_, size_t v_depth_2875_, lean_object* v_keys_2876_, lean_object* v_vals_2877_, lean_object* v_i_2878_, lean_object* v_entries_2879_){
_start:
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_array_get_size(v_keys_2876_);
v___x_2881_ = lean_nat_dec_lt(v_i_2878_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_dec(v_i_2878_);
return v_entries_2879_;
}
else
{
lean_object* v_k_2882_; lean_object* v_v_2883_; uint64_t v___x_2884_; size_t v_h_2885_; size_t v___x_2886_; lean_object* v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; size_t v_h_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_k_2882_ = lean_array_fget_borrowed(v_keys_2876_, v_i_2878_);
v_v_2883_ = lean_array_fget_borrowed(v_vals_2877_, v_i_2878_);
v___x_2884_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2874_, v_k_2882_);
v_h_2885_ = lean_uint64_to_usize(v___x_2884_);
v___x_2886_ = ((size_t)5ULL);
v___x_2887_ = lean_unsigned_to_nat(1u);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_sub(v_depth_2875_, v___x_2888_);
v___x_2890_ = lean_usize_mul(v___x_2886_, v___x_2889_);
v_h_2891_ = lean_usize_shift_right(v_h_2885_, v___x_2890_);
v___x_2892_ = lean_nat_add(v_i_2878_, v___x_2887_);
lean_dec(v_i_2878_);
lean_inc(v_v_2883_);
lean_inc(v_k_2882_);
v___x_2893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2874_, v_entries_2879_, v_h_2891_, v_depth_2875_, v_k_2882_, v_v_2883_);
v_i_2878_ = v___x_2892_;
v_entries_2879_ = v___x_2893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2895_, lean_object* v_depth_2896_, lean_object* v_keys_2897_, lean_object* v_vals_2898_, lean_object* v_i_2899_, lean_object* v_entries_2900_){
_start:
{
size_t v_depth_boxed_2901_; lean_object* v_res_2902_; 
v_depth_boxed_2901_ = lean_unbox_usize(v_depth_2896_);
lean_dec(v_depth_2896_);
v_res_2902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2895_, v_depth_boxed_2901_, v_keys_2897_, v_vals_2898_, v_i_2899_, v_entries_2900_);
lean_dec_ref(v_vals_2898_);
lean_dec_ref(v_keys_2897_);
lean_dec_ref(v___x_2895_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_){
_start:
{
size_t v_x_26409__boxed_2909_; size_t v_x_26410__boxed_2910_; lean_object* v_res_2911_; 
v_x_26409__boxed_2909_ = lean_unbox_usize(v_x_2905_);
lean_dec(v_x_2905_);
v_x_26410__boxed_2910_ = lean_unbox_usize(v_x_2906_);
lean_dec(v_x_2906_);
v_res_2911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2903_, v_x_2904_, v_x_26409__boxed_2909_, v_x_26410__boxed_2910_, v_x_2907_, v_x_2908_);
lean_dec_ref(v___x_2903_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
uint64_t v___x_2916_; size_t v___x_2917_; size_t v___x_2918_; lean_object* v___x_2919_; 
v___x_2916_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2912_, v_x_2914_);
v___x_2917_ = lean_uint64_to_usize(v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2912_, v_x_2913_, v___x_2917_, v___x_2918_, v_x_2914_, v_x_2915_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2920_, v_x_2921_, v_x_2922_, v_x_2923_);
lean_dec_ref(v___x_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2929_, lean_object* v_rootNew_2930_, uint8_t v_a_2931_, lean_object* v_a_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3126_; 
v_snd_2940_ = lean_ctor_get(v_a_2932_, 1);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_a_2932_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v_a_2932_, 0);
lean_dec(v_unused_3127_);
v___x_2942_ = v_a_2932_;
v_isShared_2943_ = v_isSharedCheck_3126_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_dec(v_a_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3126_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_st_ref_get(v___y_2933_);
lean_inc(v_snd_2940_);
v___x_2946_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2945_, v_snd_2940_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___x_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3117_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_3117_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3117_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_self_2951_; lean_object* v_next_2952_; lean_object* v_congr_2953_; lean_object* v_target_x3f_2954_; lean_object* v_proof_x3f_2955_; uint8_t v_flipped_2956_; lean_object* v_size_2957_; uint8_t v_interpreted_2958_; uint8_t v_ctor_2959_; uint8_t v_hasLambdas_2960_; uint8_t v_heqProofs_2961_; lean_object* v_idx_2962_; lean_object* v_generation_2963_; lean_object* v_mt_2964_; lean_object* v_sTerms_2965_; uint8_t v_funCC_2966_; lean_object* v_ematchDiagSource_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3115_; 
v_self_2951_ = lean_ctor_get(v_a_2947_, 0);
v_next_2952_ = lean_ctor_get(v_a_2947_, 1);
v_congr_2953_ = lean_ctor_get(v_a_2947_, 3);
v_target_x3f_2954_ = lean_ctor_get(v_a_2947_, 4);
v_proof_x3f_2955_ = lean_ctor_get(v_a_2947_, 5);
v_flipped_2956_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12);
v_size_2957_ = lean_ctor_get(v_a_2947_, 6);
v_interpreted_2958_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 1);
v_ctor_2959_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 2);
v_hasLambdas_2960_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 3);
v_heqProofs_2961_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 4);
v_idx_2962_ = lean_ctor_get(v_a_2947_, 7);
v_generation_2963_ = lean_ctor_get(v_a_2947_, 8);
v_mt_2964_ = lean_ctor_get(v_a_2947_, 9);
v_sTerms_2965_ = lean_ctor_get(v_a_2947_, 10);
v_funCC_2966_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2967_ = lean_ctor_get(v_a_2947_, 11);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v_a_2947_, 2);
lean_dec(v_unused_3116_);
v___x_2969_ = v_a_2947_;
v_isShared_2970_ = v_isSharedCheck_3115_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_ematchDiagSource_2967_);
lean_inc(v_sTerms_2965_);
lean_inc(v_mt_2964_);
lean_inc(v_generation_2963_);
lean_inc(v_idx_2962_);
lean_inc(v_size_2957_);
lean_inc(v_proof_x3f_2955_);
lean_inc(v_target_x3f_2954_);
lean_inc(v_congr_2953_);
lean_inc(v_next_2952_);
lean_inc(v_self_2951_);
lean_dec(v_a_2947_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3115_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2987_; 
lean_inc(v_ematchDiagSource_2967_);
lean_inc(v_sTerms_2965_);
lean_inc(v_mt_2964_);
lean_inc(v_generation_2963_);
lean_inc(v_idx_2962_);
lean_inc(v_size_2957_);
lean_inc(v_proof_x3f_2955_);
lean_inc(v_target_x3f_2954_);
lean_inc_ref(v_rootNew_2930_);
lean_inc_ref(v_next_2952_);
lean_inc_ref(v_self_2951_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 2, v_rootNew_2930_);
v___x_2987_ = v___x_2969_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_self_2951_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_next_2952_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_rootNew_2930_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_congr_2953_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_target_x3f_2954_);
lean_ctor_set(v_reuseFailAlloc_3114_, 5, v_proof_x3f_2955_);
lean_ctor_set(v_reuseFailAlloc_3114_, 6, v_size_2957_);
lean_ctor_set(v_reuseFailAlloc_3114_, 7, v_idx_2962_);
lean_ctor_set(v_reuseFailAlloc_3114_, 8, v_generation_2963_);
lean_ctor_set(v_reuseFailAlloc_3114_, 9, v_mt_2964_);
lean_ctor_set(v_reuseFailAlloc_3114_, 10, v_sTerms_2965_);
lean_ctor_set(v_reuseFailAlloc_3114_, 11, v_ematchDiagSource_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12, v_flipped_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12 + 1, v_interpreted_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12 + 2, v_ctor_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12 + 3, v_hasLambdas_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12 + 4, v_heqProofs_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3114_, sizeof(void*)*12 + 5, v_funCC_2966_);
v___x_2987_ = v_reuseFailAlloc_3114_;
goto v_reusejp_2986_;
}
v___jp_2971_:
{
size_t v___x_2972_; size_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_ptr_addr(v_next_2952_);
v___x_2973_ = lean_ptr_addr(v_lhs_2929_);
v___x_2974_ = lean_usize_dec_eq(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2976_; 
lean_del_object(v___x_2949_);
lean_dec(v_snd_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_next_2952_);
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2976_ = v___x_2942_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_next_2952_);
v___x_2976_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v_a_2932_ = v___x_2976_;
goto _start;
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_rootNew_2930_);
v___x_2979_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2979_);
v___x_2981_ = v___x_2942_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_snd_2940_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2981_);
v___x_2983_ = v___x_2949_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; 
lean_inc_ref(v___x_2987_);
lean_inc_ref(v_self_2951_);
v___x_2988_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2951_, v___x_2987_, v___y_2933_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
if (v_a_2931_ == 0)
{
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2989_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2990_ = lean_unsigned_to_nat(3u);
v___x_2991_ = l_Lean_Expr_isAppOfArity(v_self_2951_, v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
uint8_t v___x_2992_; 
v___x_2992_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2987_);
lean_dec_ref(v___x_2987_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v_toGoalState_2994_; lean_object* v_enodeMap_2995_; lean_object* v_congrTable_2996_; lean_object* v___x_2997_; 
v___x_2993_ = lean_st_ref_get(v___y_2933_);
v_toGoalState_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc_ref(v_toGoalState_2994_);
lean_dec(v___x_2993_);
v_enodeMap_2995_ = lean_ctor_get(v_toGoalState_2994_, 1);
lean_inc_ref(v_enodeMap_2995_);
v_congrTable_2996_ = lean_ctor_get(v_toGoalState_2994_, 4);
lean_inc_ref(v_congrTable_2996_);
lean_dec_ref(v_toGoalState_2994_);
lean_inc_ref(v_self_2951_);
v___x_2997_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2995_, v_congrTable_2996_, v_self_2951_);
lean_dec_ref(v_congrTable_2996_);
lean_dec_ref(v_enodeMap_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
lean_object* v_val_2998_; lean_object* v_fst_2999_; lean_object* v___x_3000_; 
v_val_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_val_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v_fst_2999_ = lean_ctor_get(v_val_2998_, 0);
lean_inc(v_fst_2999_);
lean_dec(v_val_2998_);
v___x_3000_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2999_, v___y_2934_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; uint8_t v___x_3002_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = lean_unbox(v_a_3001_);
lean_dec(v_a_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v_toGoalState_3004_; lean_object* v_mvarId_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3097_; 
v___x_3003_ = lean_st_ref_take(v___y_2933_);
v_toGoalState_3004_ = lean_ctor_get(v___x_3003_, 0);
v_mvarId_3005_ = lean_ctor_get(v___x_3003_, 1);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3007_ = v___x_3003_;
v_isShared_3008_ = v_isSharedCheck_3097_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_mvarId_3005_);
lean_inc(v_toGoalState_3004_);
lean_dec(v___x_3003_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3097_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_nextDeclIdx_3009_; lean_object* v_enodeMap_3010_; lean_object* v_exprs_3011_; lean_object* v_parents_3012_; lean_object* v_congrTable_3013_; lean_object* v_appMap_3014_; lean_object* v_indicesFound_3015_; lean_object* v_toProcess_3016_; lean_object* v_internalizing_3017_; uint8_t v_inconsistent_3018_; lean_object* v_nextIdx_3019_; lean_object* v_newRawFacts_3020_; lean_object* v_facts_3021_; lean_object* v_extThms_3022_; lean_object* v_ematch_3023_; lean_object* v_inj_3024_; lean_object* v_split_3025_; lean_object* v_clean_3026_; lean_object* v_sstates_3027_; lean_object* v_goalStack_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3096_; 
v_nextDeclIdx_3009_ = lean_ctor_get(v_toGoalState_3004_, 0);
v_enodeMap_3010_ = lean_ctor_get(v_toGoalState_3004_, 1);
v_exprs_3011_ = lean_ctor_get(v_toGoalState_3004_, 2);
v_parents_3012_ = lean_ctor_get(v_toGoalState_3004_, 3);
v_congrTable_3013_ = lean_ctor_get(v_toGoalState_3004_, 4);
v_appMap_3014_ = lean_ctor_get(v_toGoalState_3004_, 5);
v_indicesFound_3015_ = lean_ctor_get(v_toGoalState_3004_, 6);
v_toProcess_3016_ = lean_ctor_get(v_toGoalState_3004_, 7);
v_internalizing_3017_ = lean_ctor_get(v_toGoalState_3004_, 8);
v_inconsistent_3018_ = lean_ctor_get_uint8(v_toGoalState_3004_, sizeof(void*)*19);
v_nextIdx_3019_ = lean_ctor_get(v_toGoalState_3004_, 9);
v_newRawFacts_3020_ = lean_ctor_get(v_toGoalState_3004_, 10);
v_facts_3021_ = lean_ctor_get(v_toGoalState_3004_, 11);
v_extThms_3022_ = lean_ctor_get(v_toGoalState_3004_, 12);
v_ematch_3023_ = lean_ctor_get(v_toGoalState_3004_, 13);
v_inj_3024_ = lean_ctor_get(v_toGoalState_3004_, 14);
v_split_3025_ = lean_ctor_get(v_toGoalState_3004_, 15);
v_clean_3026_ = lean_ctor_get(v_toGoalState_3004_, 16);
v_sstates_3027_ = lean_ctor_get(v_toGoalState_3004_, 17);
v_goalStack_3028_ = lean_ctor_get(v_toGoalState_3004_, 18);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_toGoalState_3004_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3030_ = v_toGoalState_3004_;
v_isShared_3031_ = v_isSharedCheck_3096_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_goalStack_3028_);
lean_inc(v_sstates_3027_);
lean_inc(v_clean_3026_);
lean_inc(v_split_3025_);
lean_inc(v_inj_3024_);
lean_inc(v_ematch_3023_);
lean_inc(v_extThms_3022_);
lean_inc(v_facts_3021_);
lean_inc(v_newRawFacts_3020_);
lean_inc(v_nextIdx_3019_);
lean_inc(v_internalizing_3017_);
lean_inc(v_toProcess_3016_);
lean_inc(v_indicesFound_3015_);
lean_inc(v_appMap_3014_);
lean_inc(v_congrTable_3013_);
lean_inc(v_parents_3012_);
lean_inc(v_exprs_3011_);
lean_inc(v_enodeMap_3010_);
lean_inc(v_nextDeclIdx_3009_);
lean_dec(v_toGoalState_3004_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3096_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3032_ = lean_box(0);
lean_inc_ref(v_self_2951_);
v___x_3033_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3010_, v_congrTable_3013_, v_self_2951_, v___x_3032_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 4, v___x_3033_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_nextDeclIdx_3009_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_enodeMap_3010_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_exprs_3011_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_parents_3012_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3095_, 5, v_appMap_3014_);
lean_ctor_set(v_reuseFailAlloc_3095_, 6, v_indicesFound_3015_);
lean_ctor_set(v_reuseFailAlloc_3095_, 7, v_toProcess_3016_);
lean_ctor_set(v_reuseFailAlloc_3095_, 8, v_internalizing_3017_);
lean_ctor_set(v_reuseFailAlloc_3095_, 9, v_nextIdx_3019_);
lean_ctor_set(v_reuseFailAlloc_3095_, 10, v_newRawFacts_3020_);
lean_ctor_set(v_reuseFailAlloc_3095_, 11, v_facts_3021_);
lean_ctor_set(v_reuseFailAlloc_3095_, 12, v_extThms_3022_);
lean_ctor_set(v_reuseFailAlloc_3095_, 13, v_ematch_3023_);
lean_ctor_set(v_reuseFailAlloc_3095_, 14, v_inj_3024_);
lean_ctor_set(v_reuseFailAlloc_3095_, 15, v_split_3025_);
lean_ctor_set(v_reuseFailAlloc_3095_, 16, v_clean_3026_);
lean_ctor_set(v_reuseFailAlloc_3095_, 17, v_sstates_3027_);
lean_ctor_set(v_reuseFailAlloc_3095_, 18, v_goalStack_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*19, v_inconsistent_3018_);
v___x_3035_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3035_);
v___x_3037_ = v___x_3007_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_mvarId_3005_);
v___x_3037_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_st_ref_put(v___y_2933_, v___x_3037_);
lean_inc_ref(v_rootNew_2930_);
lean_inc_ref(v_next_2952_);
lean_inc_ref_n(v_self_2951_, 3);
v___x_3039_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3039_, 0, v_self_2951_);
lean_ctor_set(v___x_3039_, 1, v_next_2952_);
lean_ctor_set(v___x_3039_, 2, v_rootNew_2930_);
lean_ctor_set(v___x_3039_, 3, v_self_2951_);
lean_ctor_set(v___x_3039_, 4, v_target_x3f_2954_);
lean_ctor_set(v___x_3039_, 5, v_proof_x3f_2955_);
lean_ctor_set(v___x_3039_, 6, v_size_2957_);
lean_ctor_set(v___x_3039_, 7, v_idx_2962_);
lean_ctor_set(v___x_3039_, 8, v_generation_2963_);
lean_ctor_set(v___x_3039_, 9, v_mt_2964_);
lean_ctor_set(v___x_3039_, 10, v_sTerms_2965_);
lean_ctor_set(v___x_3039_, 11, v_ematchDiagSource_2967_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12, v_flipped_2956_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12 + 1, v_interpreted_2958_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12 + 2, v_ctor_2959_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12 + 3, v_hasLambdas_2960_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12 + 4, v_heqProofs_2961_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*12 + 5, v_funCC_2966_);
v___x_3040_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2951_, v___x_3039_, v___y_2933_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec_ref_known(v___x_3040_, 1);
v___x_3041_ = lean_st_ref_get(v___y_2933_);
lean_inc(v_fst_2999_);
v___x_3042_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3041_, v_fst_2999_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___x_3041_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_self_3044_; lean_object* v_next_3045_; lean_object* v_root_3046_; lean_object* v_target_x3f_3047_; lean_object* v_proof_x3f_3048_; uint8_t v_flipped_3049_; lean_object* v_size_3050_; uint8_t v_interpreted_3051_; uint8_t v_ctor_3052_; uint8_t v_hasLambdas_3053_; uint8_t v_heqProofs_3054_; lean_object* v_idx_3055_; lean_object* v_generation_3056_; lean_object* v_mt_3057_; lean_object* v_sTerms_3058_; uint8_t v_funCC_3059_; lean_object* v_ematchDiagSource_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3076_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v_self_3044_ = lean_ctor_get(v_a_3043_, 0);
v_next_3045_ = lean_ctor_get(v_a_3043_, 1);
v_root_3046_ = lean_ctor_get(v_a_3043_, 2);
v_target_x3f_3047_ = lean_ctor_get(v_a_3043_, 4);
v_proof_x3f_3048_ = lean_ctor_get(v_a_3043_, 5);
v_flipped_3049_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12);
v_size_3050_ = lean_ctor_get(v_a_3043_, 6);
v_interpreted_3051_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12 + 1);
v_ctor_3052_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12 + 2);
v_hasLambdas_3053_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12 + 3);
v_heqProofs_3054_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12 + 4);
v_idx_3055_ = lean_ctor_get(v_a_3043_, 7);
v_generation_3056_ = lean_ctor_get(v_a_3043_, 8);
v_mt_3057_ = lean_ctor_get(v_a_3043_, 9);
v_sTerms_3058_ = lean_ctor_get(v_a_3043_, 10);
v_funCC_3059_ = lean_ctor_get_uint8(v_a_3043_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3060_ = lean_ctor_get(v_a_3043_, 11);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_a_3043_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_a_3043_, 3);
lean_dec(v_unused_3077_);
v___x_3062_ = v_a_3043_;
v_isShared_3063_ = v_isSharedCheck_3076_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_ematchDiagSource_3060_);
lean_inc(v_sTerms_3058_);
lean_inc(v_mt_3057_);
lean_inc(v_generation_3056_);
lean_inc(v_idx_3055_);
lean_inc(v_size_3050_);
lean_inc(v_proof_x3f_3048_);
lean_inc(v_target_x3f_3047_);
lean_inc(v_root_3046_);
lean_inc(v_next_3045_);
lean_inc(v_self_3044_);
lean_dec(v_a_3043_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3076_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 3, v_self_2951_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_self_3044_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_next_3045_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_root_3046_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_self_2951_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_target_x3f_3047_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_proof_x3f_3048_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_size_3050_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_idx_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_generation_3056_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_mt_3057_);
lean_ctor_set(v_reuseFailAlloc_3075_, 10, v_sTerms_3058_);
lean_ctor_set(v_reuseFailAlloc_3075_, 11, v_ematchDiagSource_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12, v_flipped_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 1, v_interpreted_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 2, v_ctor_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 3, v_hasLambdas_3053_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 4, v_heqProofs_3054_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 5, v_funCC_3059_);
v___x_3065_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2999_, v___x_3065_, v___y_2933_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_dec_ref_known(v___x_3066_, 1);
goto v___jp_2971_;
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_next_2952_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_fst_2999_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3078_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3042_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3042_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_fst_2999_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3086_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3040_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3040_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
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
lean_dec(v_fst_2999_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_fst_2999_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3098_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3000_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3000_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3106_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_2988_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_2988_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3118_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_2946_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_2946_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3128_, lean_object* v_rootNew_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v_a_26593__boxed_3139_; lean_object* v_res_3140_; 
v_a_26593__boxed_3139_ = lean_unbox(v_a_3130_);
v_res_3140_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3128_, v_rootNew_3129_, v_a_26593__boxed_3139_, v_a_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v_lhs_3128_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3141_, lean_object* v_rootNew_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3142_, v_a_3147_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_box(0);
lean_inc_ref(v_lhs_3141_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v_lhs_3141_);
v___x_3158_ = lean_unbox(v_a_3155_);
lean_dec(v_a_3155_);
v___x_3159_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3141_, v_rootNew_3142_, v___x_3158_, v___x_3157_, v_a_3143_, v_a_3147_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
lean_dec_ref(v_lhs_3141_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3173_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3173_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_fst_3164_; 
v_fst_3164_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_fst_3164_);
lean_dec(v_a_3160_);
if (lean_obj_tag(v_fst_3164_) == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_box(0);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3165_);
v___x_3167_ = v___x_3162_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
else
{
lean_object* v_val_3169_; lean_object* v___x_3171_; 
v_val_3169_ = lean_ctor_get(v_fst_3164_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v_fst_3164_, 1);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v_val_3169_);
v___x_3171_ = v___x_3162_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_val_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
v_a_3174_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3159_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3159_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v_rootNew_3142_);
lean_dec_ref(v_lhs_3141_);
v_a_3182_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3154_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3154_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3190_, lean_object* v_rootNew_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3190_, v_rootNew_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec(v_a_3201_);
lean_dec_ref(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec(v_a_3192_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3204_, lean_object* v_00_u03b2_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3204_, v_x_3206_, v_x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3209_, lean_object* v_00_u03b2_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3209_, v_00_u03b2_3210_, v_x_3211_, v_x_3212_);
lean_dec_ref(v_x_3211_);
lean_dec_ref(v___x_3209_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3214_, lean_object* v_00_u03b2_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3214_, v_x_3216_, v_x_3217_, v_x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3220_, lean_object* v_00_u03b2_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3220_, v_00_u03b2_3221_, v_x_3222_, v_x_3223_, v_x_3224_);
lean_dec_ref(v___x_3220_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3226_, lean_object* v_rootNew_3227_, uint8_t v_a_3228_, lean_object* v_inst_3229_, lean_object* v_a_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3226_, v_rootNew_3227_, v_a_3228_, v_a_3230_, v___y_3231_, v___y_3235_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3243_, lean_object* v_rootNew_3244_, lean_object* v_a_3245_, lean_object* v_inst_3246_, lean_object* v_a_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v_a_26978__boxed_3259_; lean_object* v_res_3260_; 
v_a_26978__boxed_3259_ = lean_unbox(v_a_3245_);
v_res_3260_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3243_, v_rootNew_3244_, v_a_26978__boxed_3259_, v_inst_3246_, v_a_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v_lhs_3243_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_x_3263_, size_t v_x_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v___x_3266_; 
lean_inc_ref(v_x_3263_);
v___x_3266_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3261_, v_x_3263_, v_x_3264_, v_x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3267_, lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
size_t v_x_27021__boxed_3272_; lean_object* v_res_3273_; 
v_x_27021__boxed_3272_ = lean_unbox_usize(v_x_3270_);
lean_dec(v_x_3270_);
v_res_3273_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3267_, v_00_u03b2_3268_, v_x_3269_, v_x_27021__boxed_3272_, v_x_3271_);
lean_dec_ref(v_x_3269_);
lean_dec_ref(v___x_3267_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3274_, lean_object* v_00_u03b2_3275_, lean_object* v_x_3276_, size_t v_x_3277_, size_t v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3274_, v_x_3276_, v_x_3277_, v_x_3278_, v_x_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_, lean_object* v_x_3288_){
_start:
{
size_t v_x_27035__boxed_3289_; size_t v_x_27036__boxed_3290_; lean_object* v_res_3291_; 
v_x_27035__boxed_3289_ = lean_unbox_usize(v_x_3285_);
lean_dec(v_x_3285_);
v_x_27036__boxed_3290_ = lean_unbox_usize(v_x_3286_);
lean_dec(v_x_3286_);
v_res_3291_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3282_, v_00_u03b2_3283_, v_x_3284_, v_x_27035__boxed_3289_, v_x_27036__boxed_3290_, v_x_3287_, v_x_3288_);
lean_dec_ref(v___x_3282_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_keys_3294_, lean_object* v_vals_3295_, lean_object* v_heq_3296_, lean_object* v_i_3297_, lean_object* v_k_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3292_, v_keys_3294_, v_vals_3295_, v_i_3297_, v_k_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3300_, lean_object* v_00_u03b2_3301_, lean_object* v_keys_3302_, lean_object* v_vals_3303_, lean_object* v_heq_3304_, lean_object* v_i_3305_, lean_object* v_k_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3300_, v_00_u03b2_3301_, v_keys_3302_, v_vals_3303_, v_heq_3304_, v_i_3305_, v_k_3306_);
lean_dec_ref(v_vals_3303_);
lean_dec_ref(v_keys_3302_);
lean_dec_ref(v___x_3300_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3308_, lean_object* v_00_u03b2_3309_, lean_object* v_n_3310_, lean_object* v_k_3311_, lean_object* v_v_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3308_, v_n_3310_, v_k_3311_, v_v_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3314_, lean_object* v_00_u03b2_3315_, lean_object* v_n_3316_, lean_object* v_k_3317_, lean_object* v_v_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3314_, v_00_u03b2_3315_, v_n_3316_, v_k_3317_, v_v_3318_);
lean_dec_ref(v___x_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3320_, lean_object* v_00_u03b2_3321_, size_t v_depth_3322_, lean_object* v_keys_3323_, lean_object* v_vals_3324_, lean_object* v_heq_3325_, lean_object* v_i_3326_, lean_object* v_entries_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3320_, v_depth_3322_, v_keys_3323_, v_vals_3324_, v_i_3326_, v_entries_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3329_, lean_object* v_00_u03b2_3330_, lean_object* v_depth_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_entries_3336_){
_start:
{
size_t v_depth_boxed_3337_; lean_object* v_res_3338_; 
v_depth_boxed_3337_ = lean_unbox_usize(v_depth_3331_);
lean_dec(v_depth_3331_);
v_res_3338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3329_, v_00_u03b2_3330_, v_depth_boxed_3337_, v_keys_3332_, v_vals_3333_, v_heq_3334_, v_i_3335_, v_entries_3336_);
lean_dec_ref(v_vals_3333_);
lean_dec_ref(v_keys_3332_);
lean_dec_ref(v___x_3329_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3339_, v_x_3341_, v_x_3342_, v_x_3343_, v_x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3346_, lean_object* v_00_u03b2_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_, lean_object* v_x_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3346_, v_00_u03b2_3347_, v_x_3348_, v_x_3349_, v_x_3350_, v_x_3351_);
lean_dec_ref(v___x_3346_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
if (lean_obj_tag(v_as_x27_3353_) == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3354_);
return v___x_3366_;
}
else
{
lean_object* v_head_3367_; lean_object* v_tail_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_head_3367_ = lean_ctor_get(v_as_x27_3353_, 0);
v_tail_3368_ = lean_ctor_get(v_as_x27_3353_, 1);
v___x_3369_ = lean_box(0);
lean_inc(v_head_3367_);
v___x_3370_ = l_Lean_Meta_Grind_propagateUp(v_head_3367_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_dec_ref_known(v___x_3370_, 1);
v_as_x27_3353_ = v_tail_3368_;
v_b_3354_ = v___x_3369_;
goto _start;
}
else
{
return v___x_3370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3372_, v_b_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec(v_as_x27_3372_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3386_, lean_object* v_b_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
if (lean_obj_tag(v_as_x27_3386_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v_b_3387_);
return v___x_3399_;
}
else
{
lean_object* v_head_3400_; lean_object* v_tail_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_head_3400_ = lean_ctor_get(v_as_x27_3386_, 0);
v_tail_3401_ = lean_ctor_get(v_as_x27_3386_, 1);
v___x_3402_ = lean_box(0);
lean_inc(v_head_3400_);
v___x_3403_ = l_Lean_Meta_Grind_propagateDown(v_head_3400_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v_as_x27_3386_ = v_tail_3401_;
v_b_3387_ = v___x_3402_;
goto _start;
}
else
{
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3405_, v_b_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v_as_x27_3405_);
return v_res_3418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_cls_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3423_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3424_ = l_Lean_Name_append(v___x_3423_, v_cls_3422_);
return v___x_3424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3437_, uint8_t v_isHEq_3438_, lean_object* v_lhs_3439_, lean_object* v_rhs_3440_, lean_object* v_lhsNode_3441_, lean_object* v_rhsNode_3442_, lean_object* v_lhsRoot_3443_, lean_object* v_rhsRoot_3444_, uint8_t v_flipped_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; uint8_t v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; uint8_t v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v_toCold_3703_; lean_object* v_options_3704_; lean_object* v_inheritedTraceOptions_3705_; uint8_t v_hasTrace_3706_; lean_object* v_cls_3707_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v_fns_u2082_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v_fns_u2081_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; 
v_toCold_3703_ = lean_ctor_get(v_a_3454_, 0);
v_options_3704_ = lean_ctor_get(v_toCold_3703_, 2);
v_inheritedTraceOptions_3705_ = lean_ctor_get(v_toCold_3703_, 11);
v_hasTrace_3706_ = lean_ctor_get_uint8(v_options_3704_, sizeof(void*)*1);
v_cls_3707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3706_ == 0)
{
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3705_, v_options_3704_, v___x_3907_);
if (v___x_3908_ == 0)
{
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Meta_Grind_updateLastTag(v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref_known(v___x_3909_, 1);
lean_inc_ref(v_lhs_3439_);
v___x_3910_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3439_, v_a_3446_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
lean_inc_ref(v_rhs_3440_);
v___x_3912_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3440_, v_a_3446_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v_a_3911_);
v___x_3916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v_a_3913_);
v___x_3919_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3707_, v___x_3918_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_dec_ref_known(v___x_3919_, 1);
v___y_3827_ = v_a_3446_;
v___y_3828_ = v_a_3447_;
v___y_3829_ = v_a_3448_;
v___y_3830_ = v_a_3449_;
v___y_3831_ = v_a_3450_;
v___y_3832_ = v_a_3451_;
v___y_3833_ = v_a_3452_;
v___y_3834_ = v_a_3453_;
v___y_3835_ = v_a_3454_;
v___y_3836_ = v_a_3455_;
goto v___jp_3826_;
}
else
{
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhsNode_3441_);
lean_dec_ref(v_rhs_3440_);
lean_dec_ref(v_lhs_3439_);
lean_dec_ref(v_proof_3437_);
return v___x_3919_;
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_a_3911_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhsNode_3441_);
lean_dec_ref(v_rhs_3440_);
lean_dec_ref(v_lhs_3439_);
lean_dec_ref(v_proof_3437_);
v_a_3920_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3912_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3912_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhsNode_3441_);
lean_dec_ref(v_rhs_3440_);
lean_dec_ref(v_lhs_3439_);
lean_dec_ref(v_proof_3437_);
v_a_3928_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3910_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3910_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhsNode_3441_);
lean_dec_ref(v_rhs_3440_);
lean_dec_ref(v_lhs_3439_);
lean_dec_ref(v_proof_3437_);
return v___x_3909_;
}
}
}
v___jp_3457_:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3464_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3500_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3500_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3500_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_unbox(v_a_3475_);
lean_dec(v_a_3475_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_del_object(v___x_3477_);
v___x_3480_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3458_);
lean_dec(v___y_3458_);
v___x_3481_ = lean_box(0);
v___x_3482_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3480_, v___x_3481_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___x_3480_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3482_, 1);
v___x_3483_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3459_, v___x_3481_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref_known(v___x_3483_, 1);
v___x_3484_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3462_, v___y_3461_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3462_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3484_, 1);
v___x_3485_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3460_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3494_; 
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v___x_3485_, 0);
lean_dec(v_unused_3495_);
v___x_3487_ = v___x_3485_;
v_isShared_3488_ = v_isSharedCheck_3494_;
goto v_resetjp_3486_;
}
else
{
lean_dec(v___x_3485_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3494_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Lean_Expr_isTrue(v___y_3463_);
lean_dec_ref(v___y_3463_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3491_; 
lean_dec(v___y_3459_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3481_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3481_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
else
{
lean_object* v___x_3493_; 
lean_del_object(v___x_3487_);
v___x_3493_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3459_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3459_);
return v___x_3493_;
}
}
}
else
{
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3459_);
return v___x_3485_;
}
}
else
{
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
return v___x_3484_;
}
}
else
{
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
return v___x_3483_;
}
}
else
{
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
return v___x_3482_;
}
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec(v___y_3458_);
v___x_3496_ = lean_box(0);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3496_);
v___x_3498_ = v___x_3477_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec(v___y_3458_);
v_a_3501_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3474_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3474_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_inc_ref(v___y_3521_);
v___x_3547_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3547_, 0, v___y_3521_);
lean_ctor_set(v___x_3547_, 1, v___y_3523_);
lean_ctor_set(v___x_3547_, 2, v___y_3514_);
lean_ctor_set(v___x_3547_, 3, v___y_3528_);
lean_ctor_set(v___x_3547_, 4, v___y_3516_);
lean_ctor_set(v___x_3547_, 5, v___y_3519_);
lean_ctor_set(v___x_3547_, 6, v___y_3533_);
lean_ctor_set(v___x_3547_, 7, v___y_3545_);
lean_ctor_set(v___x_3547_, 8, v___y_3540_);
lean_ctor_set(v___x_3547_, 9, v___y_3539_);
lean_ctor_set(v___x_3547_, 10, v___y_3525_);
lean_ctor_set(v___x_3547_, 11, v___y_3537_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12, v___y_3542_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12 + 1, v___y_3511_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12 + 2, v___y_3538_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12 + 3, v___y_3546_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12 + 4, v___y_3536_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*12 + 5, v___y_3529_);
lean_inc_ref(v___y_3524_);
v___x_3548_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3524_, v___x_3547_, v___y_3541_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; 
lean_dec_ref_known(v___x_3548_, 1);
lean_inc_ref(v___y_3543_);
v___x_3549_ = l_Lean_Meta_Grind_propagateBeta(v___y_3543_, v___y_3515_, v___y_3541_, v___y_3517_, v___y_3510_, v___y_3544_, v___y_3522_, v___y_3518_, v___y_3532_, v___y_3530_, v___y_3513_, v___y_3512_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3550_; 
lean_dec_ref_known(v___x_3549_, 1);
lean_inc_ref(v___y_3520_);
v___x_3550_ = l_Lean_Meta_Grind_propagateBeta(v___y_3520_, v___y_3535_, v___y_3541_, v___y_3517_, v___y_3510_, v___y_3544_, v___y_3522_, v___y_3518_, v___y_3532_, v___y_3530_, v___y_3513_, v___y_3512_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3550_, 1);
v___x_3551_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v___y_3531_, v_lhsRoot_3443_, v___y_3536_, v___y_3541_, v___y_3532_, v___y_3530_, v___y_3513_, v___y_3512_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3534_, v___y_3541_);
lean_dec_ref(v___y_3534_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v___x_3554_; 
lean_dec_ref_known(v___x_3553_, 1);
lean_inc_ref(v___y_3524_);
v___x_3554_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3526_, v___y_3524_, v___y_3541_, v___y_3517_, v___y_3510_, v___y_3544_, v___y_3522_, v___y_3518_, v___y_3532_, v___y_3530_, v___y_3513_, v___y_3512_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v___x_3555_; 
lean_dec_ref_known(v___x_3554_, 1);
v___x_3555_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3541_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; uint8_t v___x_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = lean_unbox(v_a_3556_);
lean_dec(v_a_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
v___x_3558_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3521_, v___y_3541_, v___y_3517_, v___y_3510_, v___y_3544_, v___y_3522_, v___y_3518_, v___y_3532_, v___y_3530_, v___y_3513_, v___y_3512_);
lean_dec_ref(v___y_3521_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_dec_ref_known(v___x_3558_, 1);
v___y_3458_ = v___y_3526_;
v___y_3459_ = v___y_3527_;
v___y_3460_ = v_a_3552_;
v___y_3461_ = v___y_3520_;
v___y_3462_ = v___y_3543_;
v___y_3463_ = v___y_3524_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v___y_3517_;
v___y_3466_ = v___y_3510_;
v___y_3467_ = v___y_3544_;
v___y_3468_ = v___y_3522_;
v___y_3469_ = v___y_3518_;
v___y_3470_ = v___y_3532_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3513_;
v___y_3473_ = v___y_3512_;
goto v___jp_3457_;
}
else
{
lean_dec(v_a_3552_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3520_);
return v___x_3558_;
}
}
else
{
lean_dec_ref(v___y_3521_);
v___y_3458_ = v___y_3526_;
v___y_3459_ = v___y_3527_;
v___y_3460_ = v_a_3552_;
v___y_3461_ = v___y_3520_;
v___y_3462_ = v___y_3543_;
v___y_3463_ = v___y_3524_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v___y_3517_;
v___y_3466_ = v___y_3510_;
v___y_3467_ = v___y_3544_;
v___y_3468_ = v___y_3522_;
v___y_3469_ = v___y_3518_;
v___y_3470_ = v___y_3532_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3513_;
v___y_3473_ = v___y_3512_;
goto v___jp_3457_;
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3552_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
v_a_3559_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3555_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3555_);
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
lean_dec(v_a_3552_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v___x_3554_;
}
}
else
{
lean_dec(v_a_3552_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v___x_3553_;
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
v_a_3567_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3551_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3551_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v_lhsRoot_3443_);
return v___x_3550_;
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v_lhsRoot_3443_);
return v___x_3549_;
}
}
else
{
lean_dec_ref(v___y_3543_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_lhsRoot_3443_);
return v___x_3548_;
}
}
v___jp_3575_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_st_ref_get(v___y_3590_);
v___x_3600_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3599_, v___y_3576_, v___y_3582_, v___y_3580_, v___y_3586_, v___y_3585_);
lean_dec(v___x_3599_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_self_3602_; lean_object* v_root_3603_; lean_object* v_congr_3604_; lean_object* v_target_x3f_3605_; lean_object* v_proof_x3f_3606_; uint8_t v_flipped_3607_; lean_object* v_size_3608_; uint8_t v_interpreted_3609_; uint8_t v_ctor_3610_; uint8_t v_hasLambdas_3611_; lean_object* v_idx_3612_; lean_object* v_generation_3613_; lean_object* v_mt_3614_; lean_object* v_sTerms_3615_; uint8_t v_funCC_3616_; lean_object* v_ematchDiagSource_3617_; lean_object* v___x_3618_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v_self_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc_ref(v_self_3602_);
v_root_3603_ = lean_ctor_get(v_a_3601_, 2);
lean_inc_ref(v_root_3603_);
v_congr_3604_ = lean_ctor_get(v_a_3601_, 3);
lean_inc_ref(v_congr_3604_);
v_target_x3f_3605_ = lean_ctor_get(v_a_3601_, 4);
lean_inc(v_target_x3f_3605_);
v_proof_x3f_3606_ = lean_ctor_get(v_a_3601_, 5);
lean_inc(v_proof_x3f_3606_);
v_flipped_3607_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*12);
v_size_3608_ = lean_ctor_get(v_a_3601_, 6);
v_interpreted_3609_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*12 + 1);
v_ctor_3610_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*12 + 2);
v_hasLambdas_3611_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*12 + 3);
v_idx_3612_ = lean_ctor_get(v_a_3601_, 7);
lean_inc(v_idx_3612_);
v_generation_3613_ = lean_ctor_get(v_a_3601_, 8);
lean_inc(v_generation_3613_);
v_mt_3614_ = lean_ctor_get(v_a_3601_, 9);
lean_inc(v_mt_3614_);
v_sTerms_3615_ = lean_ctor_get(v_a_3601_, 10);
lean_inc(v_sTerms_3615_);
v_funCC_3616_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3617_ = lean_ctor_get(v_a_3601_, 11);
lean_inc(v_ematchDiagSource_3617_);
v___x_3618_ = lean_nat_add(v_size_3608_, v___y_3596_);
lean_dec(v___y_3596_);
if (v_hasLambdas_3611_ == 0)
{
v___y_3510_ = v___y_3579_;
v___y_3511_ = v_interpreted_3609_;
v___y_3512_ = v___y_3585_;
v___y_3513_ = v___y_3586_;
v___y_3514_ = v_root_3603_;
v___y_3515_ = v___y_3587_;
v___y_3516_ = v_target_x3f_3605_;
v___y_3517_ = v___y_3588_;
v___y_3518_ = v___y_3589_;
v___y_3519_ = v_proof_x3f_3606_;
v___y_3520_ = v___y_3591_;
v___y_3521_ = v_self_3602_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3597_;
v___y_3525_ = v_sTerms_3615_;
v___y_3526_ = v___y_3577_;
v___y_3527_ = v___y_3578_;
v___y_3528_ = v_congr_3604_;
v___y_3529_ = v_funCC_3616_;
v___y_3530_ = v___y_3580_;
v___y_3531_ = v_a_3601_;
v___y_3532_ = v___y_3582_;
v___y_3533_ = v___x_3618_;
v___y_3534_ = v___y_3584_;
v___y_3535_ = v___y_3583_;
v___y_3536_ = v___y_3598_;
v___y_3537_ = v_ematchDiagSource_3617_;
v___y_3538_ = v_ctor_3610_;
v___y_3539_ = v_mt_3614_;
v___y_3540_ = v_generation_3613_;
v___y_3541_ = v___y_3590_;
v___y_3542_ = v_flipped_3607_;
v___y_3543_ = v___y_3592_;
v___y_3544_ = v___y_3593_;
v___y_3545_ = v_idx_3612_;
v___y_3546_ = v___y_3581_;
goto v___jp_3509_;
}
else
{
v___y_3510_ = v___y_3579_;
v___y_3511_ = v_interpreted_3609_;
v___y_3512_ = v___y_3585_;
v___y_3513_ = v___y_3586_;
v___y_3514_ = v_root_3603_;
v___y_3515_ = v___y_3587_;
v___y_3516_ = v_target_x3f_3605_;
v___y_3517_ = v___y_3588_;
v___y_3518_ = v___y_3589_;
v___y_3519_ = v_proof_x3f_3606_;
v___y_3520_ = v___y_3591_;
v___y_3521_ = v_self_3602_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3597_;
v___y_3525_ = v_sTerms_3615_;
v___y_3526_ = v___y_3577_;
v___y_3527_ = v___y_3578_;
v___y_3528_ = v_congr_3604_;
v___y_3529_ = v_funCC_3616_;
v___y_3530_ = v___y_3580_;
v___y_3531_ = v_a_3601_;
v___y_3532_ = v___y_3582_;
v___y_3533_ = v___x_3618_;
v___y_3534_ = v___y_3584_;
v___y_3535_ = v___y_3583_;
v___y_3536_ = v___y_3598_;
v___y_3537_ = v_ematchDiagSource_3617_;
v___y_3538_ = v_ctor_3610_;
v___y_3539_ = v_mt_3614_;
v___y_3540_ = v_generation_3613_;
v___y_3541_ = v___y_3590_;
v___y_3542_ = v_flipped_3607_;
v___y_3543_ = v___y_3592_;
v___y_3544_ = v___y_3593_;
v___y_3545_ = v_idx_3612_;
v___y_3546_ = v_hasLambdas_3611_;
goto v___jp_3509_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v_lhsRoot_3443_);
v_a_3619_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3600_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3600_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
v___jp_3627_:
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3630_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
if (lean_obj_tag(v___x_3650_) == 0)
{
uint8_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec_ref_known(v___x_3650_, 1);
v___x_3651_ = 0;
v___x_3652_ = lean_st_ref_get(v___y_3640_);
v___x_3653_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3652_, v_lhs_3439_, v___x_3651_);
lean_dec(v___x_3652_);
v___x_3654_ = lean_st_ref_get(v___y_3640_);
lean_inc_ref(v___y_3637_);
v___x_3655_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3654_, v___y_3637_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___x_3654_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v_self_3657_; lean_object* v_root_3658_; lean_object* v_congr_3659_; lean_object* v_target_x3f_3660_; lean_object* v_proof_x3f_3661_; uint8_t v_flipped_3662_; lean_object* v_size_3663_; uint8_t v_interpreted_3664_; uint8_t v_ctor_3665_; uint8_t v_hasLambdas_3666_; uint8_t v_heqProofs_3667_; lean_object* v_idx_3668_; lean_object* v_generation_3669_; lean_object* v_mt_3670_; lean_object* v_sTerms_3671_; uint8_t v_funCC_3672_; lean_object* v_ematchDiagSource_3673_; lean_object* v_self_3674_; lean_object* v_next_3675_; uint8_t v_heqProofs_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3684_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v_self_3657_ = lean_ctor_get(v_a_3656_, 0);
lean_inc_ref(v_self_3657_);
v_root_3658_ = lean_ctor_get(v_a_3656_, 2);
lean_inc_ref(v_root_3658_);
v_congr_3659_ = lean_ctor_get(v_a_3656_, 3);
lean_inc_ref(v_congr_3659_);
v_target_x3f_3660_ = lean_ctor_get(v_a_3656_, 4);
lean_inc(v_target_x3f_3660_);
v_proof_x3f_3661_ = lean_ctor_get(v_a_3656_, 5);
lean_inc(v_proof_x3f_3661_);
v_flipped_3662_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12);
v_size_3663_ = lean_ctor_get(v_a_3656_, 6);
lean_inc(v_size_3663_);
v_interpreted_3664_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12 + 1);
v_ctor_3665_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12 + 2);
v_hasLambdas_3666_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12 + 3);
v_heqProofs_3667_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12 + 4);
v_idx_3668_ = lean_ctor_get(v_a_3656_, 7);
lean_inc(v_idx_3668_);
v_generation_3669_ = lean_ctor_get(v_a_3656_, 8);
lean_inc(v_generation_3669_);
v_mt_3670_ = lean_ctor_get(v_a_3656_, 9);
lean_inc(v_mt_3670_);
v_sTerms_3671_ = lean_ctor_get(v_a_3656_, 10);
lean_inc(v_sTerms_3671_);
v_funCC_3672_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3673_ = lean_ctor_get(v_a_3656_, 11);
lean_inc(v_ematchDiagSource_3673_);
lean_dec(v_a_3656_);
v_self_3674_ = lean_ctor_get(v_rhsRoot_3444_, 0);
v_next_3675_ = lean_ctor_get(v_rhsRoot_3444_, 1);
v_heqProofs_3676_ = lean_ctor_get_uint8(v_rhsRoot_3444_, sizeof(void*)*12 + 4);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_rhsRoot_3444_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; lean_object* v_unused_3688_; lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; 
v_unused_3685_ = lean_ctor_get(v_rhsRoot_3444_, 11);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_rhsRoot_3444_, 10);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_rhsRoot_3444_, 9);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_rhsRoot_3444_, 8);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_rhsRoot_3444_, 7);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_rhsRoot_3444_, 6);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_rhsRoot_3444_, 5);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_rhsRoot_3444_, 4);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_rhsRoot_3444_, 3);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_rhsRoot_3444_, 2);
lean_dec(v_unused_3694_);
v___x_3678_ = v_rhsRoot_3444_;
v_isShared_3679_ = v_isSharedCheck_3684_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_next_3675_);
lean_inc(v_self_3674_);
lean_dec(v_rhsRoot_3444_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3684_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 11, v_ematchDiagSource_3673_);
lean_ctor_set(v___x_3678_, 10, v_sTerms_3671_);
lean_ctor_set(v___x_3678_, 9, v_mt_3670_);
lean_ctor_set(v___x_3678_, 8, v_generation_3669_);
lean_ctor_set(v___x_3678_, 7, v_idx_3668_);
lean_ctor_set(v___x_3678_, 6, v_size_3663_);
lean_ctor_set(v___x_3678_, 5, v_proof_x3f_3661_);
lean_ctor_set(v___x_3678_, 4, v_target_x3f_3660_);
lean_ctor_set(v___x_3678_, 3, v_congr_3659_);
lean_ctor_set(v___x_3678_, 2, v_root_3658_);
lean_ctor_set(v___x_3678_, 0, v_self_3657_);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_self_3657_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_next_3675_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v_root_3658_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v_congr_3659_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v_target_x3f_3660_);
lean_ctor_set(v_reuseFailAlloc_3683_, 5, v_proof_x3f_3661_);
lean_ctor_set(v_reuseFailAlloc_3683_, 6, v_size_3663_);
lean_ctor_set(v_reuseFailAlloc_3683_, 7, v_idx_3668_);
lean_ctor_set(v_reuseFailAlloc_3683_, 8, v_generation_3669_);
lean_ctor_set(v_reuseFailAlloc_3683_, 9, v_mt_3670_);
lean_ctor_set(v_reuseFailAlloc_3683_, 10, v_sTerms_3671_);
lean_ctor_set(v_reuseFailAlloc_3683_, 11, v_ematchDiagSource_3673_);
v___x_3681_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12, v_flipped_3662_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12 + 1, v_interpreted_3664_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12 + 2, v_ctor_3665_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12 + 3, v_hasLambdas_3666_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12 + 4, v_heqProofs_3667_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*12 + 5, v_funCC_3672_);
v___x_3682_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3633_, v___x_3681_, v___y_3640_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
if (v_isHEq_3438_ == 0)
{
if (v_heqProofs_3676_ == 0)
{
v___y_3576_ = v_self_3674_;
v___y_3577_ = v___y_3630_;
v___y_3578_ = v___x_3653_;
v___y_3579_ = v___y_3642_;
v___y_3580_ = v___y_3647_;
v___y_3581_ = v___y_3632_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3636_;
v___y_3584_ = v___y_3637_;
v___y_3585_ = v___y_3649_;
v___y_3586_ = v___y_3648_;
v___y_3587_ = v___y_3629_;
v___y_3588_ = v___y_3641_;
v___y_3589_ = v___y_3645_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3631_;
v___y_3592_ = v___y_3634_;
v___y_3593_ = v___y_3643_;
v___y_3594_ = v___y_3635_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3638_;
v___y_3597_ = v___y_3639_;
v___y_3598_ = v___y_3628_;
goto v___jp_3575_;
}
else
{
v___y_3576_ = v_self_3674_;
v___y_3577_ = v___y_3630_;
v___y_3578_ = v___x_3653_;
v___y_3579_ = v___y_3642_;
v___y_3580_ = v___y_3647_;
v___y_3581_ = v___y_3632_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3636_;
v___y_3584_ = v___y_3637_;
v___y_3585_ = v___y_3649_;
v___y_3586_ = v___y_3648_;
v___y_3587_ = v___y_3629_;
v___y_3588_ = v___y_3641_;
v___y_3589_ = v___y_3645_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3631_;
v___y_3592_ = v___y_3634_;
v___y_3593_ = v___y_3643_;
v___y_3594_ = v___y_3635_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3638_;
v___y_3597_ = v___y_3639_;
v___y_3598_ = v_heqProofs_3676_;
goto v___jp_3575_;
}
}
else
{
v___y_3576_ = v_self_3674_;
v___y_3577_ = v___y_3630_;
v___y_3578_ = v___x_3653_;
v___y_3579_ = v___y_3642_;
v___y_3580_ = v___y_3647_;
v___y_3581_ = v___y_3632_;
v___y_3582_ = v___y_3646_;
v___y_3583_ = v___y_3636_;
v___y_3584_ = v___y_3637_;
v___y_3585_ = v___y_3649_;
v___y_3586_ = v___y_3648_;
v___y_3587_ = v___y_3629_;
v___y_3588_ = v___y_3641_;
v___y_3589_ = v___y_3645_;
v___y_3590_ = v___y_3640_;
v___y_3591_ = v___y_3631_;
v___y_3592_ = v___y_3634_;
v___y_3593_ = v___y_3643_;
v___y_3594_ = v___y_3635_;
v___y_3595_ = v___y_3644_;
v___y_3596_ = v___y_3638_;
v___y_3597_ = v___y_3639_;
v___y_3598_ = v_isHEq_3438_;
goto v___jp_3575_;
}
}
else
{
lean_dec_ref(v_self_3674_);
lean_dec(v___x_3653_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_lhsRoot_3443_);
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v___x_3653_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
v_a_3695_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3655_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3655_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
return v___x_3650_;
}
}
v___jp_3708_:
{
lean_object* v_self_3724_; lean_object* v_next_3725_; lean_object* v_size_3726_; uint8_t v_hasLambdas_3727_; uint8_t v_heqProofs_3728_; lean_object* v___x_3729_; 
v_self_3724_ = lean_ctor_get(v_lhsRoot_3443_, 0);
v_next_3725_ = lean_ctor_get(v_lhsRoot_3443_, 1);
v_size_3726_ = lean_ctor_get(v_lhsRoot_3443_, 6);
v_hasLambdas_3727_ = lean_ctor_get_uint8(v_lhsRoot_3443_, sizeof(void*)*12 + 3);
v_heqProofs_3728_ = lean_ctor_get_uint8(v_lhsRoot_3443_, sizeof(void*)*12 + 4);
v___x_3729_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3724_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v_root_3731_; lean_object* v___x_3732_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v_root_3731_ = lean_ctor_get(v_rhsNode_3442_, 2);
lean_inc_ref_n(v_root_3731_, 2);
lean_dec_ref(v_rhsNode_3442_);
lean_inc_ref(v_lhs_3439_);
v___x_3732_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3439_, v_root_3731_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_toCold_3733_; lean_object* v_options_3734_; uint8_t v_hasTrace_3735_; 
lean_dec_ref_known(v___x_3732_, 1);
v_toCold_3733_ = lean_ctor_get(v___y_3722_, 0);
v_options_3734_ = lean_ctor_get(v_toCold_3733_, 2);
v_hasTrace_3735_ = lean_ctor_get_uint8(v_options_3734_, sizeof(void*)*1);
if (v_hasTrace_3735_ == 0)
{
lean_inc(v_size_3726_);
lean_inc_ref(v_self_3724_);
lean_inc_ref(v_next_3725_);
v___y_3628_ = v_heqProofs_3728_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v_a_3730_;
v___y_3631_ = v___y_3710_;
v___y_3632_ = v_hasLambdas_3727_;
v___y_3633_ = v___y_3711_;
v___y_3634_ = v___y_3712_;
v___y_3635_ = v_next_3725_;
v___y_3636_ = v_fns_u2082_3713_;
v___y_3637_ = v_self_3724_;
v___y_3638_ = v_size_3726_;
v___y_3639_ = v_root_3731_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
goto v___jp_3627_;
}
else
{
lean_object* v_inheritedTraceOptions_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v_inheritedTraceOptions_3736_ = lean_ctor_get(v_toCold_3733_, 11);
v___x_3737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3736_, v_options_3734_, v___x_3737_);
if (v___x_3738_ == 0)
{
lean_inc(v_size_3726_);
lean_inc_ref(v_self_3724_);
lean_inc_ref(v_next_3725_);
v___y_3628_ = v_heqProofs_3728_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v_a_3730_;
v___y_3631_ = v___y_3710_;
v___y_3632_ = v_hasLambdas_3727_;
v___y_3633_ = v___y_3711_;
v___y_3634_ = v___y_3712_;
v___y_3635_ = v_next_3725_;
v___y_3636_ = v_fns_u2082_3713_;
v___y_3637_ = v_self_3724_;
v___y_3638_ = v_size_3726_;
v___y_3639_ = v_root_3731_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_Grind_updateLastTag(v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; 
lean_dec_ref_known(v___x_3739_, 1);
lean_inc_ref(v_lhs_3439_);
v___x_3740_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3439_, v___y_3714_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
lean_inc_ref(v_root_3731_);
v___x_3742_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3731_, v___y_3714_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = lean_st_ref_get(v___y_3714_);
lean_inc_ref(v_lhs_3439_);
v___x_3745_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3744_, v_lhs_3439_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___x_3744_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3746_, v___y_3714_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3747_, 1);
v___x_3749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3741_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v_a_3743_);
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v_a_3748_);
v___x_3755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3707_, v___x_3754_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_dec_ref_known(v___x_3755_, 1);
lean_inc(v_size_3726_);
lean_inc_ref(v_self_3724_);
lean_inc_ref(v_next_3725_);
v___y_3628_ = v_heqProofs_3728_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v_a_3730_;
v___y_3631_ = v___y_3710_;
v___y_3632_ = v_hasLambdas_3727_;
v___y_3633_ = v___y_3711_;
v___y_3634_ = v___y_3712_;
v___y_3635_ = v_next_3725_;
v___y_3636_ = v_fns_u2082_3713_;
v___y_3637_ = v_self_3724_;
v___y_3638_ = v_size_3726_;
v___y_3639_ = v_root_3731_;
v___y_3640_ = v___y_3714_;
v___y_3641_ = v___y_3715_;
v___y_3642_ = v___y_3716_;
v___y_3643_ = v___y_3717_;
v___y_3644_ = v___y_3718_;
v___y_3645_ = v___y_3719_;
v___y_3646_ = v___y_3720_;
v___y_3647_ = v___y_3721_;
v___y_3648_ = v___y_3722_;
v___y_3649_ = v___y_3723_;
goto v___jp_3627_;
}
else
{
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
return v___x_3755_;
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v_a_3743_);
lean_dec(v_a_3741_);
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
v_a_3756_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3747_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3747_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec(v_a_3743_);
lean_dec(v_a_3741_);
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
v_a_3764_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3745_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3745_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v_a_3741_);
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
v_a_3772_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3742_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3742_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
v_a_3780_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3740_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3740_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
return v___x_3739_;
}
}
}
}
else
{
lean_dec_ref(v_root_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_lhs_3439_);
return v___x_3732_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_fns_u2082_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
v_a_3788_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3729_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3729_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
v___jp_3796_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___x_3811_ = lean_array_get_size(v___y_3797_);
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = lean_nat_dec_eq(v___x_3811_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v_self_3814_; lean_object* v___x_3815_; 
v_self_3814_ = lean_ctor_get(v_lhsRoot_3443_, 0);
lean_inc_ref(v_self_3814_);
v___x_3815_ = l_Lean_Meta_Grind_getFnRoots(v_self_3814_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v___y_3709_ = v_fns_u2081_3800_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v_fns_u2082_3713_ = v_a_3816_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
v___y_3719_ = v___y_3806_;
v___y_3720_ = v___y_3807_;
v___y_3721_ = v___y_3808_;
v___y_3722_ = v___y_3809_;
v___y_3723_ = v___y_3810_;
goto v___jp_3708_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v_fns_u2081_3800_);
lean_dec_ref(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
v_a_3817_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3815_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3815_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v___x_3825_; 
v___x_3825_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3709_ = v_fns_u2081_3800_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
v_fns_u2082_3713_ = v___x_3825_;
v___y_3714_ = v___y_3801_;
v___y_3715_ = v___y_3802_;
v___y_3716_ = v___y_3803_;
v___y_3717_ = v___y_3804_;
v___y_3718_ = v___y_3805_;
v___y_3719_ = v___y_3806_;
v___y_3720_ = v___y_3807_;
v___y_3721_ = v___y_3808_;
v___y_3722_ = v___y_3809_;
v___y_3723_ = v___y_3810_;
goto v___jp_3708_;
}
}
v___jp_3826_:
{
lean_object* v___x_3837_; 
lean_inc_ref(v_lhs_3439_);
v___x_3837_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3439_, v___y_3827_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3905_; 
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3905_ == 0)
{
lean_object* v_unused_3906_; 
v_unused_3906_ = lean_ctor_get(v___x_3837_, 0);
lean_dec(v_unused_3906_);
v___x_3839_ = v___x_3837_;
v_isShared_3840_ = v_isSharedCheck_3905_;
goto v_resetjp_3838_;
}
else
{
lean_dec(v___x_3837_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3905_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_self_3841_; lean_object* v_next_3842_; lean_object* v_root_3843_; lean_object* v_congr_3844_; lean_object* v_size_3845_; uint8_t v_interpreted_3846_; uint8_t v_ctor_3847_; uint8_t v_hasLambdas_3848_; uint8_t v_heqProofs_3849_; lean_object* v_idx_3850_; lean_object* v_generation_3851_; lean_object* v_mt_3852_; lean_object* v_sTerms_3853_; uint8_t v_funCC_3854_; lean_object* v_ematchDiagSource_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3902_; 
v_self_3841_ = lean_ctor_get(v_lhsNode_3441_, 0);
v_next_3842_ = lean_ctor_get(v_lhsNode_3441_, 1);
v_root_3843_ = lean_ctor_get(v_lhsNode_3441_, 2);
v_congr_3844_ = lean_ctor_get(v_lhsNode_3441_, 3);
v_size_3845_ = lean_ctor_get(v_lhsNode_3441_, 6);
v_interpreted_3846_ = lean_ctor_get_uint8(v_lhsNode_3441_, sizeof(void*)*12 + 1);
v_ctor_3847_ = lean_ctor_get_uint8(v_lhsNode_3441_, sizeof(void*)*12 + 2);
v_hasLambdas_3848_ = lean_ctor_get_uint8(v_lhsNode_3441_, sizeof(void*)*12 + 3);
v_heqProofs_3849_ = lean_ctor_get_uint8(v_lhsNode_3441_, sizeof(void*)*12 + 4);
v_idx_3850_ = lean_ctor_get(v_lhsNode_3441_, 7);
v_generation_3851_ = lean_ctor_get(v_lhsNode_3441_, 8);
v_mt_3852_ = lean_ctor_get(v_lhsNode_3441_, 9);
v_sTerms_3853_ = lean_ctor_get(v_lhsNode_3441_, 10);
v_funCC_3854_ = lean_ctor_get_uint8(v_lhsNode_3441_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3855_ = lean_ctor_get(v_lhsNode_3441_, 11);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_lhsNode_3441_);
if (v_isSharedCheck_3902_ == 0)
{
lean_object* v_unused_3903_; lean_object* v_unused_3904_; 
v_unused_3903_ = lean_ctor_get(v_lhsNode_3441_, 5);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_lhsNode_3441_, 4);
lean_dec(v_unused_3904_);
v___x_3857_ = v_lhsNode_3441_;
v_isShared_3858_ = v_isSharedCheck_3902_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_ematchDiagSource_3855_);
lean_inc(v_sTerms_3853_);
lean_inc(v_mt_3852_);
lean_inc(v_generation_3851_);
lean_inc(v_idx_3850_);
lean_inc(v_size_3845_);
lean_inc(v_congr_3844_);
lean_inc(v_root_3843_);
lean_inc(v_next_3842_);
lean_inc(v_self_3841_);
lean_dec(v_lhsNode_3441_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3902_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set_tag(v___x_3839_, 1);
lean_ctor_set(v___x_3839_, 0, v_rhs_3440_);
v___x_3860_ = v___x_3839_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_rhs_3440_);
v___x_3860_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_proof_3437_);
lean_inc_ref(v_root_3843_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 5, v___x_3861_);
lean_ctor_set(v___x_3857_, 4, v___x_3860_);
v___x_3863_ = v___x_3857_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_self_3841_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_next_3842_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_root_3843_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_congr_3844_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3900_, 5, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3900_, 6, v_size_3845_);
lean_ctor_set(v_reuseFailAlloc_3900_, 7, v_idx_3850_);
lean_ctor_set(v_reuseFailAlloc_3900_, 8, v_generation_3851_);
lean_ctor_set(v_reuseFailAlloc_3900_, 9, v_mt_3852_);
lean_ctor_set(v_reuseFailAlloc_3900_, 10, v_sTerms_3853_);
lean_ctor_set(v_reuseFailAlloc_3900_, 11, v_ematchDiagSource_3855_);
lean_ctor_set_uint8(v_reuseFailAlloc_3900_, sizeof(void*)*12 + 1, v_interpreted_3846_);
lean_ctor_set_uint8(v_reuseFailAlloc_3900_, sizeof(void*)*12 + 2, v_ctor_3847_);
lean_ctor_set_uint8(v_reuseFailAlloc_3900_, sizeof(void*)*12 + 3, v_hasLambdas_3848_);
lean_ctor_set_uint8(v_reuseFailAlloc_3900_, sizeof(void*)*12 + 4, v_heqProofs_3849_);
lean_ctor_set_uint8(v_reuseFailAlloc_3900_, sizeof(void*)*12 + 5, v_funCC_3854_);
v___x_3863_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*12, v_flipped_3445_);
lean_inc_ref(v_lhs_3439_);
v___x_3864_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3439_, v___x_3863_, v___y_3827_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3865_; 
lean_dec_ref_known(v___x_3864_, 1);
v___x_3865_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3443_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3867_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3865_, 1);
v___x_3867_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3444_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3869_ = lean_array_get_size(v_a_3866_);
v___x_3870_ = lean_unsigned_to_nat(0u);
v___x_3871_ = lean_nat_dec_eq(v___x_3869_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v_self_3872_; lean_object* v___x_3873_; 
v_self_3872_ = lean_ctor_get(v_rhsRoot_3444_, 0);
lean_inc_ref(v_self_3872_);
v___x_3873_ = l_Lean_Meta_Grind_getFnRoots(v_self_3872_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___y_3797_ = v_a_3868_;
v___y_3798_ = v_root_3843_;
v___y_3799_ = v_a_3866_;
v_fns_u2081_3800_ = v_a_3874_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
v___y_3806_ = v___y_3832_;
v___y_3807_ = v___y_3833_;
v___y_3808_ = v___y_3834_;
v___y_3809_ = v___y_3835_;
v___y_3810_ = v___y_3836_;
goto v___jp_3796_;
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_a_3868_);
lean_dec(v_a_3866_);
lean_dec_ref(v_root_3843_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
v_a_3875_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3873_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3873_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_object* v___x_3883_; 
v___x_3883_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3797_ = v_a_3868_;
v___y_3798_ = v_root_3843_;
v___y_3799_ = v_a_3866_;
v_fns_u2081_3800_ = v___x_3883_;
v___y_3801_ = v___y_3827_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3829_;
v___y_3804_ = v___y_3830_;
v___y_3805_ = v___y_3831_;
v___y_3806_ = v___y_3832_;
v___y_3807_ = v___y_3833_;
v___y_3808_ = v___y_3834_;
v___y_3809_ = v___y_3835_;
v___y_3810_ = v___y_3836_;
goto v___jp_3796_;
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3866_);
lean_dec_ref(v_root_3843_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
v_a_3884_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3867_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3867_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v_root_3843_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
v_a_3892_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3865_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3865_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_dec_ref(v_root_3843_);
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhs_3439_);
return v___x_3864_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3444_);
lean_dec_ref(v_lhsRoot_3443_);
lean_dec_ref(v_rhsNode_3442_);
lean_dec_ref(v_lhsNode_3441_);
lean_dec_ref(v_rhs_3440_);
lean_dec_ref(v_lhs_3439_);
lean_dec_ref(v_proof_3437_);
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3936_ = _args[0];
lean_object* v_isHEq_3937_ = _args[1];
lean_object* v_lhs_3938_ = _args[2];
lean_object* v_rhs_3939_ = _args[3];
lean_object* v_lhsNode_3940_ = _args[4];
lean_object* v_rhsNode_3941_ = _args[5];
lean_object* v_lhsRoot_3942_ = _args[6];
lean_object* v_rhsRoot_3943_ = _args[7];
lean_object* v_flipped_3944_ = _args[8];
lean_object* v_a_3945_ = _args[9];
lean_object* v_a_3946_ = _args[10];
lean_object* v_a_3947_ = _args[11];
lean_object* v_a_3948_ = _args[12];
lean_object* v_a_3949_ = _args[13];
lean_object* v_a_3950_ = _args[14];
lean_object* v_a_3951_ = _args[15];
lean_object* v_a_3952_ = _args[16];
lean_object* v_a_3953_ = _args[17];
lean_object* v_a_3954_ = _args[18];
lean_object* v_a_3955_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3956_; uint8_t v_flipped_boxed_3957_; lean_object* v_res_3958_; 
v_isHEq_boxed_3956_ = lean_unbox(v_isHEq_3937_);
v_flipped_boxed_3957_ = lean_unbox(v_flipped_3944_);
v_res_3958_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3936_, v_isHEq_boxed_3956_, v_lhs_3938_, v_rhs_3939_, v_lhsNode_3940_, v_rhsNode_3941_, v_lhsRoot_3942_, v_rhsRoot_3943_, v_flipped_boxed_3957_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec(v_a_3945_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3959_, lean_object* v_as_x27_3960_, lean_object* v_b_3961_, lean_object* v_a_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3960_, v_b_3961_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3975_, lean_object* v_as_x27_3976_, lean_object* v_b_3977_, lean_object* v_a_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3975_, v_as_x27_3976_, v_b_3977_, v_a_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec(v_as_x27_3976_);
lean_dec(v_as_3975_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3991_, lean_object* v_as_x27_3992_, lean_object* v_b_3993_, lean_object* v_a_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3992_, v_b_3993_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4007_, lean_object* v_as_x27_4008_, lean_object* v_b_4009_, lean_object* v_a_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4007_, v_as_x27_4008_, v_b_4009_, v_a_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec(v_as_x27_4008_);
lean_dec(v_as_4007_);
return v_res_4022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4025_ = l_Lean_stringToMessageData(v___x_4024_);
return v___x_4025_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4031_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4032_ = l_Lean_Name_append(v___x_4031_, v___x_4030_);
return v___x_4032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4035_ = l_Lean_stringToMessageData(v___x_4034_);
return v___x_4035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4038_ = l_Lean_stringToMessageData(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4039_, lean_object* v_rhs_4040_, lean_object* v_proof_4041_, uint8_t v_isHEq_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_st_ref_get(v_a_4043_);
lean_inc_ref(v_lhs_4039_);
v___x_4058_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4057_, v_lhs_4039_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v___x_4057_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v___x_4060_ = lean_st_ref_get(v_a_4043_);
lean_inc_ref(v_rhs_4040_);
v___x_4061_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4060_, v_rhs_4040_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v___x_4060_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v_root_4063_; lean_object* v_root_4064_; size_t v___x_4065_; size_t v___x_4066_; uint8_t v___x_4067_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v_root_4063_ = lean_ctor_get(v_a_4059_, 2);
v_root_4064_ = lean_ctor_get(v_a_4062_, 2);
v___x_4065_ = lean_ptr_addr(v_root_4063_);
v___x_4066_ = lean_ptr_addr(v_root_4064_);
v___x_4067_ = lean_usize_dec_eq(v___x_4065_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v_toCold_4068_; lean_object* v_options_4069_; lean_object* v_inheritedTraceOptions_4070_; uint8_t v_hasTrace_4071_; uint8_t v___x_4072_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4110_; lean_object* v___y_4111_; uint8_t v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4168_; lean_object* v___y_4169_; uint8_t v___y_4170_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; uint8_t v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; uint8_t v___y_4197_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; uint8_t v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; uint8_t v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v_size_4228_; uint8_t v_interpreted_4229_; uint8_t v_ctor_4230_; lean_object* v___y_4231_; uint8_t v___y_4232_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; uint8_t v_ctor_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; lean_object* v___y_4258_; lean_object* v___y_4259_; uint8_t v_valueInconsistency_4260_; uint8_t v_trueEqFalse_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; 
v_toCold_4068_ = lean_ctor_get(v_a_4051_, 0);
v_options_4069_ = lean_ctor_get(v_toCold_4068_, 2);
v_inheritedTraceOptions_4070_ = lean_ctor_get(v_toCold_4068_, 11);
v_hasTrace_4071_ = lean_ctor_get_uint8(v_options_4069_, sizeof(void*)*1);
v___x_4072_ = 1;
if (v_hasTrace_4071_ == 0)
{
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
v___y_4322_ = v_a_4048_;
v___y_4323_ = v_a_4049_;
v___y_4324_ = v_a_4050_;
v___y_4325_ = v_a_4051_;
v___y_4326_ = v_a_4052_;
goto v___jp_4316_;
}
else
{
lean_object* v___x_4360_; lean_object* v_____do__lift_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___x_4375_; uint8_t v___x_4376_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4376_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4070_, v_options_4069_, v___x_4375_);
if (v___x_4376_ == 0)
{
v___y_4317_ = v_a_4043_;
v___y_4318_ = v_a_4044_;
v___y_4319_ = v_a_4045_;
v___y_4320_ = v_a_4046_;
v___y_4321_ = v_a_4047_;
v___y_4322_ = v_a_4048_;
v___y_4323_ = v_a_4049_;
v___y_4324_ = v_a_4050_;
v___y_4325_ = v_a_4051_;
v___y_4326_ = v_a_4052_;
goto v___jp_4316_;
}
else
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Meta_Grind_updateLastTag(v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_dec_ref_known(v___x_4377_, 1);
if (v_isHEq_4042_ == 0)
{
lean_object* v___x_4378_; 
lean_inc_ref(v_rhs_4040_);
lean_inc_ref(v_lhs_4039_);
v___x_4378_ = l_Lean_Meta_mkEq(v_lhs_4039_, v_rhs_4040_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
v_____do__lift_4362_ = v_a_4379_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
v___y_4368_ = v_a_4048_;
v___y_4369_ = v_a_4049_;
v___y_4370_ = v_a_4050_;
v___y_4371_ = v_a_4051_;
v___y_4372_ = v_a_4052_;
goto v___jp_4361_;
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4380_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4378_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4378_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v___x_4388_; 
lean_inc_ref(v_rhs_4040_);
lean_inc_ref(v_lhs_4039_);
v___x_4388_ = l_Lean_Meta_mkHEq(v_lhs_4039_, v_rhs_4040_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_____do__lift_4362_ = v_a_4389_;
v___y_4363_ = v_a_4043_;
v___y_4364_ = v_a_4044_;
v___y_4365_ = v_a_4045_;
v___y_4366_ = v_a_4046_;
v___y_4367_ = v_a_4047_;
v___y_4368_ = v_a_4048_;
v___y_4369_ = v_a_4049_;
v___y_4370_ = v_a_4050_;
v___y_4371_ = v_a_4051_;
v___y_4372_ = v_a_4052_;
goto v___jp_4361_;
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4390_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4388_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4388_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
else
{
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
return v___x_4377_;
}
}
v___jp_4361_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = l_Lean_MessageData_ofExpr(v_____do__lift_4362_);
v___x_4374_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4360_, v___x_4373_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_dec_ref_known(v___x_4374_, 1);
v___y_4317_ = v___y_4363_;
v___y_4318_ = v___y_4364_;
v___y_4319_ = v___y_4365_;
v___y_4320_ = v___y_4366_;
v___y_4321_ = v___y_4367_;
v___y_4322_ = v___y_4368_;
v___y_4323_ = v___y_4369_;
v___y_4324_ = v___y_4370_;
v___y_4325_ = v___y_4371_;
v___y_4326_ = v___y_4372_;
goto v___jp_4316_;
}
else
{
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
return v___x_4374_;
}
}
}
v___jp_4073_:
{
lean_object* v_toCold_4084_; lean_object* v_options_4085_; uint8_t v_hasTrace_4086_; 
v_toCold_4084_ = lean_ctor_get(v___y_4082_, 0);
v_options_4085_ = lean_ctor_get(v_toCold_4084_, 2);
v_hasTrace_4086_ = lean_ctor_get_uint8(v_options_4085_, sizeof(void*)*1);
if (v_hasTrace_4086_ == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_Meta_Grind_checkInvariants(v___x_4067_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4087_;
}
else
{
lean_object* v_inheritedTraceOptions_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v_inheritedTraceOptions_4088_ = lean_ctor_get(v_toCold_4084_, 11);
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4088_, v_options_4085_, v___x_4090_);
if (v___x_4091_ == 0)
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_Meta_Grind_checkInvariants(v___x_4067_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4092_;
}
else
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_Meta_Grind_updateLastTag(v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec_ref_known(v___x_4093_, 1);
v___x_4094_ = lean_st_ref_get(v___y_4074_);
v___x_4095_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4094_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___x_4094_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v_a_4096_);
v___x_4099_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4089_, v___x_4098_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v___x_4100_; 
lean_dec_ref_known(v___x_4099_, 1);
v___x_4100_ = l_Lean_Meta_Grind_checkInvariants(v___x_4067_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
return v___x_4100_;
}
else
{
return v___x_4099_;
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4095_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4095_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
return v___x_4093_;
}
}
}
}
v___jp_4109_:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4113_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; uint8_t v___x_4125_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v___x_4125_ = lean_unbox(v_a_4124_);
lean_dec(v_a_4124_);
if (v___x_4125_ == 0)
{
if (v___y_4112_ == 0)
{
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
goto v___jp_4073_;
}
else
{
lean_object* v_self_4126_; lean_object* v_self_4127_; lean_object* v___x_4128_; 
v_self_4126_ = lean_ctor_get(v___y_4110_, 0);
lean_inc_ref(v_self_4126_);
lean_dec_ref(v___y_4110_);
v_self_4127_ = lean_ctor_get(v___y_4111_, 0);
lean_inc_ref(v_self_4127_);
lean_dec_ref(v___y_4111_);
v___x_4128_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4126_, v_self_4127_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_dec_ref_known(v___x_4128_, 1);
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
goto v___jp_4073_;
}
else
{
return v___x_4128_;
}
}
}
else
{
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
v___y_4074_ = v___y_4113_;
v___y_4075_ = v___y_4114_;
v___y_4076_ = v___y_4115_;
v___y_4077_ = v___y_4116_;
v___y_4078_ = v___y_4117_;
v___y_4079_ = v___y_4118_;
v___y_4080_ = v___y_4119_;
v___y_4081_ = v___y_4120_;
v___y_4082_ = v___y_4121_;
v___y_4083_ = v___y_4122_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4110_);
v_a_4129_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4123_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4123_);
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
v___jp_4137_:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4141_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; uint8_t v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = lean_unbox(v_a_4152_);
lean_dec(v_a_4152_);
if (v___x_4153_ == 0)
{
uint8_t v_ctor_4154_; 
v_ctor_4154_ = lean_ctor_get_uint8(v___y_4138_, sizeof(void*)*12 + 2);
if (v_ctor_4154_ == 0)
{
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
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
goto v___jp_4109_;
}
else
{
uint8_t v_ctor_4155_; 
v_ctor_4155_ = lean_ctor_get_uint8(v___y_4139_, sizeof(void*)*12 + 2);
if (v_ctor_4155_ == 0)
{
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
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
goto v___jp_4109_;
}
else
{
lean_object* v_self_4156_; lean_object* v_self_4157_; lean_object* v___x_4158_; 
v_self_4156_ = lean_ctor_get(v___y_4138_, 0);
v_self_4157_ = lean_ctor_get(v___y_4139_, 0);
lean_inc_ref(v_self_4157_);
lean_inc_ref(v_self_4156_);
v___x_4158_ = l_Lean_Meta_Grind_propagateCtor(v_self_4156_, v_self_4157_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_dec_ref_known(v___x_4158_, 1);
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
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
goto v___jp_4109_;
}
else
{
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___y_4138_);
return v___x_4158_;
}
}
}
}
else
{
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
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
goto v___jp_4109_;
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___y_4138_);
v_a_4159_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4151_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4151_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
v___jp_4167_:
{
if (v___y_4171_ == 0)
{
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v___y_4170_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
goto v___jp_4137_;
}
else
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_dec_ref_known(v___x_4182_, 1);
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v___y_4170_;
v___y_4141_ = v___y_4172_;
v___y_4142_ = v___y_4173_;
v___y_4143_ = v___y_4174_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4176_;
v___y_4146_ = v___y_4177_;
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
goto v___jp_4137_;
}
else
{
lean_dec_ref(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v___x_4182_;
}
}
}
v___jp_4183_:
{
lean_object* v___x_4198_; 
lean_inc_ref(v___y_4194_);
lean_inc_ref(v___y_4195_);
v___x_4198_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4041_, v_isHEq_4042_, v_rhs_4040_, v_lhs_4039_, v_a_4062_, v_a_4059_, v___y_4195_, v___y_4194_, v___x_4072_, v___y_4192_, v___y_4185_, v___y_4189_, v___y_4193_, v___y_4196_, v___y_4191_, v___y_4187_, v___y_4184_, v___y_4186_, v___y_4188_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_dec_ref_known(v___x_4198_, 1);
v___y_4168_ = v___y_4194_;
v___y_4169_ = v___y_4195_;
v___y_4170_ = v___y_4190_;
v___y_4171_ = v___y_4197_;
v___y_4172_ = v___y_4192_;
v___y_4173_ = v___y_4185_;
v___y_4174_ = v___y_4189_;
v___y_4175_ = v___y_4193_;
v___y_4176_ = v___y_4196_;
v___y_4177_ = v___y_4191_;
v___y_4178_ = v___y_4187_;
v___y_4179_ = v___y_4184_;
v___y_4180_ = v___y_4186_;
v___y_4181_ = v___y_4188_;
goto v___jp_4167_;
}
else
{
lean_dec_ref(v___y_4195_);
lean_dec_ref(v___y_4194_);
return v___x_4198_;
}
}
v___jp_4199_:
{
lean_object* v___x_4214_; 
lean_inc_ref(v___y_4211_);
lean_inc_ref(v___y_4210_);
v___x_4214_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4041_, v_isHEq_4042_, v_lhs_4039_, v_rhs_4040_, v_a_4059_, v_a_4062_, v___y_4210_, v___y_4211_, v___x_4067_, v___y_4208_, v___y_4201_, v___y_4205_, v___y_4209_, v___y_4212_, v___y_4207_, v___y_4203_, v___y_4200_, v___y_4202_, v___y_4204_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_dec_ref_known(v___x_4214_, 1);
v___y_4168_ = v___y_4210_;
v___y_4169_ = v___y_4211_;
v___y_4170_ = v___y_4206_;
v___y_4171_ = v___y_4213_;
v___y_4172_ = v___y_4208_;
v___y_4173_ = v___y_4201_;
v___y_4174_ = v___y_4205_;
v___y_4175_ = v___y_4209_;
v___y_4176_ = v___y_4212_;
v___y_4177_ = v___y_4207_;
v___y_4178_ = v___y_4203_;
v___y_4179_ = v___y_4200_;
v___y_4180_ = v___y_4202_;
v___y_4181_ = v___y_4204_;
goto v___jp_4167_;
}
else
{
lean_dec_ref(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v___x_4214_;
}
}
v___jp_4215_:
{
lean_object* v_size_4233_; uint8_t v___x_4234_; 
v_size_4233_ = lean_ctor_get(v___y_4226_, 6);
v___x_4234_ = lean_nat_dec_lt(v_size_4228_, v_size_4233_);
lean_dec(v_size_4228_);
if (v___x_4234_ == 0)
{
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4225_;
v___y_4210_ = v___y_4226_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
goto v___jp_4199_;
}
else
{
if (v_interpreted_4229_ == 0)
{
if (v_ctor_4230_ == 0)
{
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4217_;
v___y_4186_ = v___y_4218_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4220_;
v___y_4189_ = v___y_4221_;
v___y_4190_ = v___y_4222_;
v___y_4191_ = v___y_4223_;
v___y_4192_ = v___y_4224_;
v___y_4193_ = v___y_4225_;
v___y_4194_ = v___y_4226_;
v___y_4195_ = v___y_4227_;
v___y_4196_ = v___y_4231_;
v___y_4197_ = v___y_4232_;
goto v___jp_4183_;
}
else
{
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4225_;
v___y_4210_ = v___y_4226_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
goto v___jp_4199_;
}
}
else
{
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4217_;
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v___y_4204_ = v___y_4220_;
v___y_4205_ = v___y_4221_;
v___y_4206_ = v___y_4222_;
v___y_4207_ = v___y_4223_;
v___y_4208_ = v___y_4224_;
v___y_4209_ = v___y_4225_;
v___y_4210_ = v___y_4226_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4231_;
v___y_4213_ = v___y_4232_;
goto v___jp_4199_;
}
}
}
v___jp_4235_:
{
if (v_ctor_4247_ == 0)
{
lean_object* v_size_4251_; uint8_t v_interpreted_4252_; uint8_t v_ctor_4253_; 
v_size_4251_ = lean_ctor_get(v___y_4248_, 6);
lean_inc(v_size_4251_);
v_interpreted_4252_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 1);
v_ctor_4253_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 2);
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___y_4245_;
v___y_4226_ = v___y_4246_;
v___y_4227_ = v___y_4248_;
v_size_4228_ = v_size_4251_;
v_interpreted_4229_ = v_interpreted_4252_;
v_ctor_4230_ = v_ctor_4253_;
v___y_4231_ = v___y_4249_;
v___y_4232_ = v___y_4250_;
goto v___jp_4215_;
}
else
{
uint8_t v_ctor_4254_; 
v_ctor_4254_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 2);
if (v_ctor_4254_ == 0)
{
v___y_4184_ = v___y_4236_;
v___y_4185_ = v___y_4237_;
v___y_4186_ = v___y_4238_;
v___y_4187_ = v___y_4239_;
v___y_4188_ = v___y_4240_;
v___y_4189_ = v___y_4241_;
v___y_4190_ = v___y_4242_;
v___y_4191_ = v___y_4243_;
v___y_4192_ = v___y_4244_;
v___y_4193_ = v___y_4245_;
v___y_4194_ = v___y_4246_;
v___y_4195_ = v___y_4248_;
v___y_4196_ = v___y_4249_;
v___y_4197_ = v___y_4250_;
goto v___jp_4183_;
}
else
{
lean_object* v_size_4255_; uint8_t v_interpreted_4256_; 
v_size_4255_ = lean_ctor_get(v___y_4248_, 6);
lean_inc(v_size_4255_);
v_interpreted_4256_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 1);
v___y_4216_ = v___y_4236_;
v___y_4217_ = v___y_4237_;
v___y_4218_ = v___y_4238_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___y_4241_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4243_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___y_4245_;
v___y_4226_ = v___y_4246_;
v___y_4227_ = v___y_4248_;
v_size_4228_ = v_size_4255_;
v_interpreted_4229_ = v_interpreted_4256_;
v_ctor_4230_ = v_ctor_4254_;
v___y_4231_ = v___y_4249_;
v___y_4232_ = v___y_4250_;
goto v___jp_4215_;
}
}
}
v___jp_4257_:
{
uint8_t v_interpreted_4272_; 
v_interpreted_4272_ = lean_ctor_get_uint8(v___y_4258_, sizeof(void*)*12 + 1);
if (v_interpreted_4272_ == 0)
{
uint8_t v_ctor_4273_; 
v_ctor_4273_ = lean_ctor_get_uint8(v___y_4258_, sizeof(void*)*12 + 2);
v___y_4236_ = v___y_4269_;
v___y_4237_ = v___y_4263_;
v___y_4238_ = v___y_4270_;
v___y_4239_ = v___y_4268_;
v___y_4240_ = v___y_4271_;
v___y_4241_ = v___y_4264_;
v___y_4242_ = v_valueInconsistency_4260_;
v___y_4243_ = v___y_4267_;
v___y_4244_ = v___y_4262_;
v___y_4245_ = v___y_4265_;
v___y_4246_ = v___y_4258_;
v_ctor_4247_ = v_ctor_4273_;
v___y_4248_ = v___y_4259_;
v___y_4249_ = v___y_4266_;
v___y_4250_ = v_trueEqFalse_4261_;
goto v___jp_4235_;
}
else
{
uint8_t v_interpreted_4274_; 
v_interpreted_4274_ = lean_ctor_get_uint8(v___y_4259_, sizeof(void*)*12 + 1);
if (v_interpreted_4274_ == 0)
{
v___y_4184_ = v___y_4269_;
v___y_4185_ = v___y_4263_;
v___y_4186_ = v___y_4270_;
v___y_4187_ = v___y_4268_;
v___y_4188_ = v___y_4271_;
v___y_4189_ = v___y_4264_;
v___y_4190_ = v_valueInconsistency_4260_;
v___y_4191_ = v___y_4267_;
v___y_4192_ = v___y_4262_;
v___y_4193_ = v___y_4265_;
v___y_4194_ = v___y_4258_;
v___y_4195_ = v___y_4259_;
v___y_4196_ = v___y_4266_;
v___y_4197_ = v_trueEqFalse_4261_;
goto v___jp_4183_;
}
else
{
uint8_t v_ctor_4275_; 
v_ctor_4275_ = lean_ctor_get_uint8(v___y_4258_, sizeof(void*)*12 + 2);
v___y_4236_ = v___y_4269_;
v___y_4237_ = v___y_4263_;
v___y_4238_ = v___y_4270_;
v___y_4239_ = v___y_4268_;
v___y_4240_ = v___y_4271_;
v___y_4241_ = v___y_4264_;
v___y_4242_ = v_valueInconsistency_4260_;
v___y_4243_ = v___y_4267_;
v___y_4244_ = v___y_4262_;
v___y_4245_ = v___y_4265_;
v___y_4246_ = v___y_4258_;
v_ctor_4247_ = v_ctor_4275_;
v___y_4248_ = v___y_4259_;
v___y_4249_ = v___y_4266_;
v___y_4250_ = v_trueEqFalse_4261_;
goto v___jp_4235_;
}
}
}
v___jp_4276_:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4283_, v___y_4278_, v___y_4286_, v___y_4288_, v___y_4277_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_dec_ref_known(v___x_4289_, 1);
v___y_4258_ = v___y_4285_;
v___y_4259_ = v___y_4287_;
v_valueInconsistency_4260_ = v___x_4067_;
v_trueEqFalse_4261_ = v___x_4072_;
v___y_4262_ = v___y_4283_;
v___y_4263_ = v___y_4282_;
v___y_4264_ = v___y_4279_;
v___y_4265_ = v___y_4284_;
v___y_4266_ = v___y_4280_;
v___y_4267_ = v___y_4281_;
v___y_4268_ = v___y_4278_;
v___y_4269_ = v___y_4286_;
v___y_4270_ = v___y_4288_;
v___y_4271_ = v___y_4277_;
goto v___jp_4257_;
}
else
{
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4285_);
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
return v___x_4289_;
}
}
v___jp_4290_:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_Meta_Grind_hasSameType(v___y_4304_, v___y_4298_, v___y_4292_, v___y_4302_, v___y_4303_, v___y_4291_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; uint8_t v___x_4307_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___x_4307_ = lean_unbox(v_a_4306_);
lean_dec(v_a_4306_);
if (v___x_4307_ == 0)
{
v___y_4258_ = v___y_4300_;
v___y_4259_ = v___y_4301_;
v_valueInconsistency_4260_ = v___x_4067_;
v_trueEqFalse_4261_ = v___x_4067_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___y_4296_;
v___y_4264_ = v___y_4293_;
v___y_4265_ = v___y_4299_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4292_;
v___y_4269_ = v___y_4302_;
v___y_4270_ = v___y_4303_;
v___y_4271_ = v___y_4291_;
goto v___jp_4257_;
}
else
{
v___y_4258_ = v___y_4300_;
v___y_4259_ = v___y_4301_;
v_valueInconsistency_4260_ = v___x_4072_;
v_trueEqFalse_4261_ = v___x_4067_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___y_4296_;
v___y_4264_ = v___y_4293_;
v___y_4265_ = v___y_4299_;
v___y_4266_ = v___y_4294_;
v___y_4267_ = v___y_4295_;
v___y_4268_ = v___y_4292_;
v___y_4269_ = v___y_4302_;
v___y_4270_ = v___y_4303_;
v___y_4271_ = v___y_4291_;
goto v___jp_4257_;
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4308_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4305_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4305_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
v___jp_4316_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_st_ref_get(v___y_4317_);
lean_inc_ref(v_root_4063_);
v___x_4328_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4327_, v_root_4063_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___x_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4330_ = lean_st_ref_get(v___y_4317_);
lean_inc_ref(v_root_4064_);
v___x_4331_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4330_, v_root_4064_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___x_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
uint8_t v_interpreted_4332_; 
v_interpreted_4332_ = lean_ctor_get_uint8(v_a_4329_, sizeof(void*)*12 + 1);
if (v_interpreted_4332_ == 0)
{
lean_object* v_a_4333_; uint8_t v_ctor_4334_; 
v_a_4333_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4331_, 1);
v_ctor_4334_ = lean_ctor_get_uint8(v_a_4329_, sizeof(void*)*12 + 2);
v___y_4236_ = v___y_4324_;
v___y_4237_ = v___y_4318_;
v___y_4238_ = v___y_4325_;
v___y_4239_ = v___y_4323_;
v___y_4240_ = v___y_4326_;
v___y_4241_ = v___y_4319_;
v___y_4242_ = v___x_4067_;
v___y_4243_ = v___y_4322_;
v___y_4244_ = v___y_4317_;
v___y_4245_ = v___y_4320_;
v___y_4246_ = v_a_4329_;
v_ctor_4247_ = v_ctor_4334_;
v___y_4248_ = v_a_4333_;
v___y_4249_ = v___y_4321_;
v___y_4250_ = v___x_4067_;
goto v___jp_4235_;
}
else
{
lean_object* v_a_4335_; uint8_t v_interpreted_4336_; 
v_a_4335_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4331_, 1);
v_interpreted_4336_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 1);
if (v_interpreted_4336_ == 0)
{
v___y_4184_ = v___y_4324_;
v___y_4185_ = v___y_4318_;
v___y_4186_ = v___y_4325_;
v___y_4187_ = v___y_4323_;
v___y_4188_ = v___y_4326_;
v___y_4189_ = v___y_4319_;
v___y_4190_ = v___x_4067_;
v___y_4191_ = v___y_4322_;
v___y_4192_ = v___y_4317_;
v___y_4193_ = v___y_4320_;
v___y_4194_ = v_a_4329_;
v___y_4195_ = v_a_4335_;
v___y_4196_ = v___y_4321_;
v___y_4197_ = v___x_4067_;
goto v___jp_4183_;
}
else
{
lean_object* v_self_4337_; uint8_t v_ctor_4338_; uint8_t v_heqProofs_4339_; lean_object* v_self_4340_; uint8_t v_heqProofs_4341_; uint8_t v___x_4342_; 
v_self_4337_ = lean_ctor_get(v_a_4329_, 0);
v_ctor_4338_ = lean_ctor_get_uint8(v_a_4329_, sizeof(void*)*12 + 2);
v_heqProofs_4339_ = lean_ctor_get_uint8(v_a_4329_, sizeof(void*)*12 + 4);
v_self_4340_ = lean_ctor_get(v_a_4335_, 0);
v_heqProofs_4341_ = lean_ctor_get_uint8(v_a_4335_, sizeof(void*)*12 + 4);
v___x_4342_ = l_Lean_Expr_isTrue(v_root_4063_);
if (v___x_4342_ == 0)
{
uint8_t v___x_4343_; 
v___x_4343_ = l_Lean_Expr_isTrue(v_root_4064_);
if (v___x_4343_ == 0)
{
if (v_isHEq_4042_ == 0)
{
if (v_heqProofs_4339_ == 0)
{
if (v_heqProofs_4341_ == 0)
{
v___y_4236_ = v___y_4324_;
v___y_4237_ = v___y_4318_;
v___y_4238_ = v___y_4325_;
v___y_4239_ = v___y_4323_;
v___y_4240_ = v___y_4326_;
v___y_4241_ = v___y_4319_;
v___y_4242_ = v___x_4072_;
v___y_4243_ = v___y_4322_;
v___y_4244_ = v___y_4317_;
v___y_4245_ = v___y_4320_;
v___y_4246_ = v_a_4329_;
v_ctor_4247_ = v_ctor_4338_;
v___y_4248_ = v_a_4335_;
v___y_4249_ = v___y_4321_;
v___y_4250_ = v___x_4067_;
goto v___jp_4235_;
}
else
{
lean_inc_ref(v_self_4340_);
lean_inc_ref(v_self_4337_);
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4323_;
v___y_4293_ = v___y_4319_;
v___y_4294_ = v___y_4321_;
v___y_4295_ = v___y_4322_;
v___y_4296_ = v___y_4318_;
v___y_4297_ = v___y_4317_;
v___y_4298_ = v_self_4340_;
v___y_4299_ = v___y_4320_;
v___y_4300_ = v_a_4329_;
v___y_4301_ = v_a_4335_;
v___y_4302_ = v___y_4324_;
v___y_4303_ = v___y_4325_;
v___y_4304_ = v_self_4337_;
goto v___jp_4290_;
}
}
else
{
lean_inc_ref(v_self_4340_);
lean_inc_ref(v_self_4337_);
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4323_;
v___y_4293_ = v___y_4319_;
v___y_4294_ = v___y_4321_;
v___y_4295_ = v___y_4322_;
v___y_4296_ = v___y_4318_;
v___y_4297_ = v___y_4317_;
v___y_4298_ = v_self_4340_;
v___y_4299_ = v___y_4320_;
v___y_4300_ = v_a_4329_;
v___y_4301_ = v_a_4335_;
v___y_4302_ = v___y_4324_;
v___y_4303_ = v___y_4325_;
v___y_4304_ = v_self_4337_;
goto v___jp_4290_;
}
}
else
{
lean_inc_ref(v_self_4340_);
lean_inc_ref(v_self_4337_);
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4323_;
v___y_4293_ = v___y_4319_;
v___y_4294_ = v___y_4321_;
v___y_4295_ = v___y_4322_;
v___y_4296_ = v___y_4318_;
v___y_4297_ = v___y_4317_;
v___y_4298_ = v_self_4340_;
v___y_4299_ = v___y_4320_;
v___y_4300_ = v_a_4329_;
v___y_4301_ = v_a_4335_;
v___y_4302_ = v___y_4324_;
v___y_4303_ = v___y_4325_;
v___y_4304_ = v_self_4337_;
goto v___jp_4290_;
}
}
else
{
v___y_4277_ = v___y_4326_;
v___y_4278_ = v___y_4323_;
v___y_4279_ = v___y_4319_;
v___y_4280_ = v___y_4321_;
v___y_4281_ = v___y_4322_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4317_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v_a_4329_;
v___y_4286_ = v___y_4324_;
v___y_4287_ = v_a_4335_;
v___y_4288_ = v___y_4325_;
goto v___jp_4276_;
}
}
else
{
v___y_4277_ = v___y_4326_;
v___y_4278_ = v___y_4323_;
v___y_4279_ = v___y_4319_;
v___y_4280_ = v___y_4321_;
v___y_4281_ = v___y_4322_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4317_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v_a_4329_;
v___y_4286_ = v___y_4324_;
v___y_4287_ = v_a_4335_;
v___y_4288_ = v___y_4325_;
goto v___jp_4276_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_a_4329_);
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4344_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4331_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4331_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4352_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4328_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4328_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
else
{
lean_object* v_toCold_4398_; lean_object* v_options_4399_; uint8_t v_hasTrace_4400_; 
lean_dec(v_a_4062_);
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
v_toCold_4398_ = lean_ctor_get(v_a_4051_, 0);
v_options_4399_ = lean_ctor_get(v_toCold_4398_, 2);
v_hasTrace_4400_ = lean_ctor_get_uint8(v_options_4399_, sizeof(void*)*1);
if (v_hasTrace_4400_ == 0)
{
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
goto v___jp_4054_;
}
else
{
lean_object* v_inheritedTraceOptions_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; uint8_t v___x_4404_; 
v_inheritedTraceOptions_4401_ = lean_ctor_get(v_toCold_4398_, 11);
v___x_4402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4404_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4401_, v_options_4399_, v___x_4403_);
if (v___x_4404_ == 0)
{
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
goto v___jp_4054_;
}
else
{
lean_object* v___x_4405_; 
v___x_4405_ = l_Lean_Meta_Grind_updateLastTag(v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4406_; 
lean_dec_ref_known(v___x_4405_, 1);
v___x_4406_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4039_, v_a_4043_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4040_, v_a_4043_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___x_4410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4411_, 0, v_a_4407_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v_a_4409_);
v___x_4413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4402_, v___x_4414_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_dec_ref_known(v___x_4415_, 1);
goto v___jp_4054_;
}
else
{
return v___x_4415_;
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec(v_a_4407_);
v_a_4416_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4408_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4408_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v_rhs_4040_);
v_a_4424_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4406_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4406_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
return v___x_4405_;
}
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_a_4059_);
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4432_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4061_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4061_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec_ref(v_proof_4041_);
lean_dec_ref(v_rhs_4040_);
lean_dec_ref(v_lhs_4039_);
v_a_4440_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4058_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4058_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
v___jp_4054_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_box(0);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4448_, lean_object* v_rhs_4449_, lean_object* v_proof_4450_, lean_object* v_isHEq_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
uint8_t v_isHEq_boxed_4463_; lean_object* v_res_4464_; 
v_isHEq_boxed_4463_ = lean_unbox(v_isHEq_4451_);
v_res_4464_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4448_, v_rhs_4449_, v_proof_4450_, v_isHEq_boxed_4463_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
lean_dec_ref(v_a_4456_);
lean_dec(v_a_4455_);
lean_dec_ref(v_a_4454_);
lean_dec(v_a_4453_);
lean_dec(v_a_4452_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v_toGoalState_4470_; lean_object* v_mvarId_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4509_; 
v___x_4469_ = lean_st_ref_take(v_a_4467_);
v_toGoalState_4470_ = lean_ctor_get(v___x_4469_, 0);
v_mvarId_4471_ = lean_ctor_get(v___x_4469_, 1);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4473_ = v___x_4469_;
v_isShared_4474_ = v_isSharedCheck_4509_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_mvarId_4471_);
lean_inc(v_toGoalState_4470_);
lean_dec(v___x_4469_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4509_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_nextDeclIdx_4475_; lean_object* v_enodeMap_4476_; lean_object* v_exprs_4477_; lean_object* v_parents_4478_; lean_object* v_congrTable_4479_; lean_object* v_appMap_4480_; lean_object* v_indicesFound_4481_; lean_object* v_internalizing_4482_; uint8_t v_inconsistent_4483_; lean_object* v_nextIdx_4484_; lean_object* v_newRawFacts_4485_; lean_object* v_facts_4486_; lean_object* v_extThms_4487_; lean_object* v_ematch_4488_; lean_object* v_inj_4489_; lean_object* v_split_4490_; lean_object* v_clean_4491_; lean_object* v_sstates_4492_; lean_object* v_goalStack_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4507_; 
v_nextDeclIdx_4475_ = lean_ctor_get(v_toGoalState_4470_, 0);
v_enodeMap_4476_ = lean_ctor_get(v_toGoalState_4470_, 1);
v_exprs_4477_ = lean_ctor_get(v_toGoalState_4470_, 2);
v_parents_4478_ = lean_ctor_get(v_toGoalState_4470_, 3);
v_congrTable_4479_ = lean_ctor_get(v_toGoalState_4470_, 4);
v_appMap_4480_ = lean_ctor_get(v_toGoalState_4470_, 5);
v_indicesFound_4481_ = lean_ctor_get(v_toGoalState_4470_, 6);
v_internalizing_4482_ = lean_ctor_get(v_toGoalState_4470_, 8);
v_inconsistent_4483_ = lean_ctor_get_uint8(v_toGoalState_4470_, sizeof(void*)*19);
v_nextIdx_4484_ = lean_ctor_get(v_toGoalState_4470_, 9);
v_newRawFacts_4485_ = lean_ctor_get(v_toGoalState_4470_, 10);
v_facts_4486_ = lean_ctor_get(v_toGoalState_4470_, 11);
v_extThms_4487_ = lean_ctor_get(v_toGoalState_4470_, 12);
v_ematch_4488_ = lean_ctor_get(v_toGoalState_4470_, 13);
v_inj_4489_ = lean_ctor_get(v_toGoalState_4470_, 14);
v_split_4490_ = lean_ctor_get(v_toGoalState_4470_, 15);
v_clean_4491_ = lean_ctor_get(v_toGoalState_4470_, 16);
v_sstates_4492_ = lean_ctor_get(v_toGoalState_4470_, 17);
v_goalStack_4493_ = lean_ctor_get(v_toGoalState_4470_, 18);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_toGoalState_4470_);
if (v_isSharedCheck_4507_ == 0)
{
lean_object* v_unused_4508_; 
v_unused_4508_ = lean_ctor_get(v_toGoalState_4470_, 7);
lean_dec(v_unused_4508_);
v___x_4495_ = v_toGoalState_4470_;
v_isShared_4496_ = v_isSharedCheck_4507_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_goalStack_4493_);
lean_inc(v_sstates_4492_);
lean_inc(v_clean_4491_);
lean_inc(v_split_4490_);
lean_inc(v_inj_4489_);
lean_inc(v_ematch_4488_);
lean_inc(v_extThms_4487_);
lean_inc(v_facts_4486_);
lean_inc(v_newRawFacts_4485_);
lean_inc(v_nextIdx_4484_);
lean_inc(v_internalizing_4482_);
lean_inc(v_indicesFound_4481_);
lean_inc(v_appMap_4480_);
lean_inc(v_congrTable_4479_);
lean_inc(v_parents_4478_);
lean_inc(v_exprs_4477_);
lean_inc(v_enodeMap_4476_);
lean_inc(v_nextDeclIdx_4475_);
lean_dec(v_toGoalState_4470_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4507_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4497_ = lean_box(0);
v___x_4498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 7, v___x_4498_);
v___x_4500_ = v___x_4495_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_nextDeclIdx_4475_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_enodeMap_4476_);
lean_ctor_set(v_reuseFailAlloc_4506_, 2, v_exprs_4477_);
lean_ctor_set(v_reuseFailAlloc_4506_, 3, v_parents_4478_);
lean_ctor_set(v_reuseFailAlloc_4506_, 4, v_congrTable_4479_);
lean_ctor_set(v_reuseFailAlloc_4506_, 5, v_appMap_4480_);
lean_ctor_set(v_reuseFailAlloc_4506_, 6, v_indicesFound_4481_);
lean_ctor_set(v_reuseFailAlloc_4506_, 7, v___x_4498_);
lean_ctor_set(v_reuseFailAlloc_4506_, 8, v_internalizing_4482_);
lean_ctor_set(v_reuseFailAlloc_4506_, 9, v_nextIdx_4484_);
lean_ctor_set(v_reuseFailAlloc_4506_, 10, v_newRawFacts_4485_);
lean_ctor_set(v_reuseFailAlloc_4506_, 11, v_facts_4486_);
lean_ctor_set(v_reuseFailAlloc_4506_, 12, v_extThms_4487_);
lean_ctor_set(v_reuseFailAlloc_4506_, 13, v_ematch_4488_);
lean_ctor_set(v_reuseFailAlloc_4506_, 14, v_inj_4489_);
lean_ctor_set(v_reuseFailAlloc_4506_, 15, v_split_4490_);
lean_ctor_set(v_reuseFailAlloc_4506_, 16, v_clean_4491_);
lean_ctor_set(v_reuseFailAlloc_4506_, 17, v_sstates_4492_);
lean_ctor_set(v_reuseFailAlloc_4506_, 18, v_goalStack_4493_);
lean_ctor_set_uint8(v_reuseFailAlloc_4506_, sizeof(void*)*19, v_inconsistent_4483_);
v___x_4500_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4502_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4500_);
v___x_4502_ = v___x_4473_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4500_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_mvarId_4471_);
v___x_4502_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_st_ref_put(v_a_4467_, v___x_4502_);
v___x_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4497_);
return v___x_4504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4510_);
lean_dec(v_a_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4513_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec(v_a_4525_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; lean_object* v_toGoalState_4540_; lean_object* v_toProcess_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4539_ = lean_st_ref_get(v_a_4537_);
v_toGoalState_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_toGoalState_4540_);
lean_dec(v___x_4539_);
v_toProcess_4541_ = lean_ctor_get(v_toGoalState_4540_, 7);
lean_inc_ref(v_toProcess_4541_);
lean_dec_ref(v_toGoalState_4540_);
v___x_4542_ = lean_array_get_size(v_toProcess_4541_);
v___x_4543_ = lean_unsigned_to_nat(1u);
v___x_4544_ = lean_nat_sub(v___x_4542_, v___x_4543_);
v___x_4545_ = lean_nat_dec_lt(v___x_4544_, v___x_4542_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec(v___x_4544_);
lean_dec_ref(v_toProcess_4541_);
v___x_4546_ = lean_box(0);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
return v___x_4547_;
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v_toGoalState_4551_; lean_object* v_mvarId_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4589_; 
v___x_4548_ = lean_array_fget(v_toProcess_4541_, v___x_4544_);
lean_dec(v___x_4544_);
lean_dec_ref(v_toProcess_4541_);
v___x_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
v___x_4550_ = lean_st_ref_take(v_a_4537_);
v_toGoalState_4551_ = lean_ctor_get(v___x_4550_, 0);
v_mvarId_4552_ = lean_ctor_get(v___x_4550_, 1);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4554_ = v___x_4550_;
v_isShared_4555_ = v_isSharedCheck_4589_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_mvarId_4552_);
lean_inc(v_toGoalState_4551_);
lean_dec(v___x_4550_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4589_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v_nextDeclIdx_4556_; lean_object* v_enodeMap_4557_; lean_object* v_exprs_4558_; lean_object* v_parents_4559_; lean_object* v_congrTable_4560_; lean_object* v_appMap_4561_; lean_object* v_indicesFound_4562_; lean_object* v_toProcess_4563_; lean_object* v_internalizing_4564_; uint8_t v_inconsistent_4565_; lean_object* v_nextIdx_4566_; lean_object* v_newRawFacts_4567_; lean_object* v_facts_4568_; lean_object* v_extThms_4569_; lean_object* v_ematch_4570_; lean_object* v_inj_4571_; lean_object* v_split_4572_; lean_object* v_clean_4573_; lean_object* v_sstates_4574_; lean_object* v_goalStack_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4588_; 
v_nextDeclIdx_4556_ = lean_ctor_get(v_toGoalState_4551_, 0);
v_enodeMap_4557_ = lean_ctor_get(v_toGoalState_4551_, 1);
v_exprs_4558_ = lean_ctor_get(v_toGoalState_4551_, 2);
v_parents_4559_ = lean_ctor_get(v_toGoalState_4551_, 3);
v_congrTable_4560_ = lean_ctor_get(v_toGoalState_4551_, 4);
v_appMap_4561_ = lean_ctor_get(v_toGoalState_4551_, 5);
v_indicesFound_4562_ = lean_ctor_get(v_toGoalState_4551_, 6);
v_toProcess_4563_ = lean_ctor_get(v_toGoalState_4551_, 7);
v_internalizing_4564_ = lean_ctor_get(v_toGoalState_4551_, 8);
v_inconsistent_4565_ = lean_ctor_get_uint8(v_toGoalState_4551_, sizeof(void*)*19);
v_nextIdx_4566_ = lean_ctor_get(v_toGoalState_4551_, 9);
v_newRawFacts_4567_ = lean_ctor_get(v_toGoalState_4551_, 10);
v_facts_4568_ = lean_ctor_get(v_toGoalState_4551_, 11);
v_extThms_4569_ = lean_ctor_get(v_toGoalState_4551_, 12);
v_ematch_4570_ = lean_ctor_get(v_toGoalState_4551_, 13);
v_inj_4571_ = lean_ctor_get(v_toGoalState_4551_, 14);
v_split_4572_ = lean_ctor_get(v_toGoalState_4551_, 15);
v_clean_4573_ = lean_ctor_get(v_toGoalState_4551_, 16);
v_sstates_4574_ = lean_ctor_get(v_toGoalState_4551_, 17);
v_goalStack_4575_ = lean_ctor_get(v_toGoalState_4551_, 18);
v_isSharedCheck_4588_ = !lean_is_exclusive(v_toGoalState_4551_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4577_ = v_toGoalState_4551_;
v_isShared_4578_ = v_isSharedCheck_4588_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_goalStack_4575_);
lean_inc(v_sstates_4574_);
lean_inc(v_clean_4573_);
lean_inc(v_split_4572_);
lean_inc(v_inj_4571_);
lean_inc(v_ematch_4570_);
lean_inc(v_extThms_4569_);
lean_inc(v_facts_4568_);
lean_inc(v_newRawFacts_4567_);
lean_inc(v_nextIdx_4566_);
lean_inc(v_internalizing_4564_);
lean_inc(v_toProcess_4563_);
lean_inc(v_indicesFound_4562_);
lean_inc(v_appMap_4561_);
lean_inc(v_congrTable_4560_);
lean_inc(v_parents_4559_);
lean_inc(v_exprs_4558_);
lean_inc(v_enodeMap_4557_);
lean_inc(v_nextDeclIdx_4556_);
lean_dec(v_toGoalState_4551_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4588_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4579_ = lean_array_pop(v_toProcess_4563_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 7, v___x_4579_);
v___x_4581_ = v___x_4577_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_nextDeclIdx_4556_);
lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_enodeMap_4557_);
lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_exprs_4558_);
lean_ctor_set(v_reuseFailAlloc_4587_, 3, v_parents_4559_);
lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_congrTable_4560_);
lean_ctor_set(v_reuseFailAlloc_4587_, 5, v_appMap_4561_);
lean_ctor_set(v_reuseFailAlloc_4587_, 6, v_indicesFound_4562_);
lean_ctor_set(v_reuseFailAlloc_4587_, 7, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4587_, 8, v_internalizing_4564_);
lean_ctor_set(v_reuseFailAlloc_4587_, 9, v_nextIdx_4566_);
lean_ctor_set(v_reuseFailAlloc_4587_, 10, v_newRawFacts_4567_);
lean_ctor_set(v_reuseFailAlloc_4587_, 11, v_facts_4568_);
lean_ctor_set(v_reuseFailAlloc_4587_, 12, v_extThms_4569_);
lean_ctor_set(v_reuseFailAlloc_4587_, 13, v_ematch_4570_);
lean_ctor_set(v_reuseFailAlloc_4587_, 14, v_inj_4571_);
lean_ctor_set(v_reuseFailAlloc_4587_, 15, v_split_4572_);
lean_ctor_set(v_reuseFailAlloc_4587_, 16, v_clean_4573_);
lean_ctor_set(v_reuseFailAlloc_4587_, 17, v_sstates_4574_);
lean_ctor_set(v_reuseFailAlloc_4587_, 18, v_goalStack_4575_);
lean_ctor_set_uint8(v_reuseFailAlloc_4587_, sizeof(void*)*19, v_inconsistent_4565_);
v___x_4581_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4583_; 
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4581_);
v___x_4583_ = v___x_4554_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_mvarId_4552_);
v___x_4583_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = lean_st_ref_put(v_a_4537_, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4549_);
return v___x_4585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4590_);
lean_dec(v_a_4590_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4593_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec(v_a_4605_);
return v_res_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4617_, lean_object* v_rhs_4618_, lean_object* v_proof_4619_, uint8_t v_isHEq_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v___x_4632_; 
v___x_4632_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4617_, v_rhs_4618_, v_proof_4619_, v_isHEq_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v___x_4633_; 
lean_dec_ref_known(v___x_4632_, 1);
lean_inc(v_a_4630_);
lean_inc_ref(v_a_4629_);
lean_inc(v_a_4628_);
lean_inc_ref(v_a_4627_);
lean_inc(v_a_4626_);
lean_inc_ref(v_a_4625_);
lean_inc(v_a_4624_);
lean_inc_ref(v_a_4623_);
lean_inc(v_a_4622_);
lean_inc(v_a_4621_);
v___x_4633_ = lean_grind_process_to_do(v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
return v___x_4633_;
}
else
{
return v___x_4632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4634_, lean_object* v_rhs_4635_, lean_object* v_proof_4636_, lean_object* v_isHEq_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_){
_start:
{
uint8_t v_isHEq_boxed_4649_; lean_object* v_res_4650_; 
v_isHEq_boxed_4649_ = lean_unbox(v_isHEq_4637_);
v_res_4650_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4634_, v_rhs_4635_, v_proof_4636_, v_isHEq_boxed_4649_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec(v_a_4638_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4651_, lean_object* v_rhs_4652_, lean_object* v_proof_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
uint8_t v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = 0;
v___x_4666_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4651_, v_rhs_4652_, v_proof_4653_, v___x_4665_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4667_, lean_object* v_rhs_4668_, lean_object* v_proof_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4667_, v_rhs_4668_, v_proof_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec(v_a_4670_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4682_, lean_object* v_rhs_4683_, lean_object* v_proof_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
uint8_t v___x_4696_; lean_object* v___x_4697_; 
v___x_4696_ = 1;
v___x_4697_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4682_, v_rhs_4683_, v_proof_4684_, v___x_4696_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4698_, lean_object* v_rhs_4699_, lean_object* v_proof_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4698_, v_rhs_4699_, v_proof_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec(v_a_4701_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v___x_4716_; lean_object* v_toGoalState_4717_; lean_object* v_mvarId_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4756_; 
v___x_4716_ = lean_st_ref_take(v_a_4714_);
v_toGoalState_4717_ = lean_ctor_get(v___x_4716_, 0);
v_mvarId_4718_ = lean_ctor_get(v___x_4716_, 1);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4720_ = v___x_4716_;
v_isShared_4721_ = v_isSharedCheck_4756_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_mvarId_4718_);
lean_inc(v_toGoalState_4717_);
lean_dec(v___x_4716_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4756_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_nextDeclIdx_4722_; lean_object* v_enodeMap_4723_; lean_object* v_exprs_4724_; lean_object* v_parents_4725_; lean_object* v_congrTable_4726_; lean_object* v_appMap_4727_; lean_object* v_indicesFound_4728_; lean_object* v_toProcess_4729_; lean_object* v_internalizing_4730_; uint8_t v_inconsistent_4731_; lean_object* v_nextIdx_4732_; lean_object* v_newRawFacts_4733_; lean_object* v_facts_4734_; lean_object* v_extThms_4735_; lean_object* v_ematch_4736_; lean_object* v_inj_4737_; lean_object* v_split_4738_; lean_object* v_clean_4739_; lean_object* v_sstates_4740_; lean_object* v_goalStack_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4755_; 
v_nextDeclIdx_4722_ = lean_ctor_get(v_toGoalState_4717_, 0);
v_enodeMap_4723_ = lean_ctor_get(v_toGoalState_4717_, 1);
v_exprs_4724_ = lean_ctor_get(v_toGoalState_4717_, 2);
v_parents_4725_ = lean_ctor_get(v_toGoalState_4717_, 3);
v_congrTable_4726_ = lean_ctor_get(v_toGoalState_4717_, 4);
v_appMap_4727_ = lean_ctor_get(v_toGoalState_4717_, 5);
v_indicesFound_4728_ = lean_ctor_get(v_toGoalState_4717_, 6);
v_toProcess_4729_ = lean_ctor_get(v_toGoalState_4717_, 7);
v_internalizing_4730_ = lean_ctor_get(v_toGoalState_4717_, 8);
v_inconsistent_4731_ = lean_ctor_get_uint8(v_toGoalState_4717_, sizeof(void*)*19);
v_nextIdx_4732_ = lean_ctor_get(v_toGoalState_4717_, 9);
v_newRawFacts_4733_ = lean_ctor_get(v_toGoalState_4717_, 10);
v_facts_4734_ = lean_ctor_get(v_toGoalState_4717_, 11);
v_extThms_4735_ = lean_ctor_get(v_toGoalState_4717_, 12);
v_ematch_4736_ = lean_ctor_get(v_toGoalState_4717_, 13);
v_inj_4737_ = lean_ctor_get(v_toGoalState_4717_, 14);
v_split_4738_ = lean_ctor_get(v_toGoalState_4717_, 15);
v_clean_4739_ = lean_ctor_get(v_toGoalState_4717_, 16);
v_sstates_4740_ = lean_ctor_get(v_toGoalState_4717_, 17);
v_goalStack_4741_ = lean_ctor_get(v_toGoalState_4717_, 18);
v_isSharedCheck_4755_ = !lean_is_exclusive(v_toGoalState_4717_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4743_ = v_toGoalState_4717_;
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_goalStack_4741_);
lean_inc(v_sstates_4740_);
lean_inc(v_clean_4739_);
lean_inc(v_split_4738_);
lean_inc(v_inj_4737_);
lean_inc(v_ematch_4736_);
lean_inc(v_extThms_4735_);
lean_inc(v_facts_4734_);
lean_inc(v_newRawFacts_4733_);
lean_inc(v_nextIdx_4732_);
lean_inc(v_internalizing_4730_);
lean_inc(v_toProcess_4729_);
lean_inc(v_indicesFound_4728_);
lean_inc(v_appMap_4727_);
lean_inc(v_congrTable_4726_);
lean_inc(v_parents_4725_);
lean_inc(v_exprs_4724_);
lean_inc(v_enodeMap_4723_);
lean_inc(v_nextDeclIdx_4722_);
lean_dec(v_toGoalState_4717_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4755_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4748_; 
v___x_4745_ = lean_box(0);
v___x_4746_ = l_Lean_PersistentArray_push___redArg(v_facts_4734_, v_fact_4713_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 11, v___x_4746_);
v___x_4748_ = v___x_4743_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_nextDeclIdx_4722_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_enodeMap_4723_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_exprs_4724_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_parents_4725_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v_congrTable_4726_);
lean_ctor_set(v_reuseFailAlloc_4754_, 5, v_appMap_4727_);
lean_ctor_set(v_reuseFailAlloc_4754_, 6, v_indicesFound_4728_);
lean_ctor_set(v_reuseFailAlloc_4754_, 7, v_toProcess_4729_);
lean_ctor_set(v_reuseFailAlloc_4754_, 8, v_internalizing_4730_);
lean_ctor_set(v_reuseFailAlloc_4754_, 9, v_nextIdx_4732_);
lean_ctor_set(v_reuseFailAlloc_4754_, 10, v_newRawFacts_4733_);
lean_ctor_set(v_reuseFailAlloc_4754_, 11, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4754_, 12, v_extThms_4735_);
lean_ctor_set(v_reuseFailAlloc_4754_, 13, v_ematch_4736_);
lean_ctor_set(v_reuseFailAlloc_4754_, 14, v_inj_4737_);
lean_ctor_set(v_reuseFailAlloc_4754_, 15, v_split_4738_);
lean_ctor_set(v_reuseFailAlloc_4754_, 16, v_clean_4739_);
lean_ctor_set(v_reuseFailAlloc_4754_, 17, v_sstates_4740_);
lean_ctor_set(v_reuseFailAlloc_4754_, 18, v_goalStack_4741_);
lean_ctor_set_uint8(v_reuseFailAlloc_4754_, sizeof(void*)*19, v_inconsistent_4731_);
v___x_4748_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4750_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 0, v___x_4748_);
v___x_4750_ = v___x_4720_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4748_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_mvarId_4718_);
v___x_4750_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = lean_st_ref_put(v_a_4714_, v___x_4750_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4745_);
return v___x_4752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4757_, v_a_4758_);
lean_dec(v_a_4758_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4761_, v_a_4762_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v_res_4786_; 
v_res_4786_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
lean_dec(v_a_4776_);
lean_dec(v_a_4775_);
return v_res_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4787_, lean_object* v_rhs_4788_, lean_object* v_proof_4789_, lean_object* v_generation_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v___x_4802_; 
lean_inc_ref(v_rhs_4788_);
lean_inc_ref(v_lhs_4787_);
v___x_4802_ = l_Lean_Meta_mkEq(v_lhs_4787_, v_rhs_4788_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4814_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc_n(v_a_4803_, 2);
lean_dec_ref_known(v___x_4802_, 1);
v___x_4804_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4803_, v_a_4791_);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4814_ == 0)
{
lean_object* v_unused_4815_; 
v_unused_4815_ = lean_ctor_get(v___x_4804_, 0);
lean_dec(v_unused_4815_);
v___x_4806_ = v___x_4804_;
v_isShared_4807_ = v_isSharedCheck_4814_;
goto v_resetjp_4805_;
}
else
{
lean_dec(v___x_4804_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4814_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
lean_ctor_set_tag(v___x_4806_, 1);
lean_ctor_set(v___x_4806_, 0, v_a_4803_);
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4803_);
v___x_4809_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4810_; 
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
lean_inc(v_a_4796_);
lean_inc_ref(v_a_4795_);
lean_inc(v_a_4794_);
lean_inc_ref(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc(v_a_4791_);
lean_inc_ref(v___x_4809_);
lean_inc(v_generation_4790_);
lean_inc_ref(v_lhs_4787_);
v___x_4810_ = lean_grind_internalize(v_lhs_4787_, v_generation_4790_, v___x_4809_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v___x_4811_; 
lean_dec_ref_known(v___x_4810_, 1);
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
lean_inc(v_a_4796_);
lean_inc_ref(v_a_4795_);
lean_inc(v_a_4794_);
lean_inc_ref(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc(v_a_4791_);
lean_inc_ref(v_rhs_4788_);
v___x_4811_ = lean_grind_internalize(v_rhs_4788_, v_generation_4790_, v___x_4809_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v___x_4812_; 
lean_dec_ref_known(v___x_4811_, 1);
v___x_4812_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4787_, v_rhs_4788_, v_proof_4789_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
return v___x_4812_;
}
else
{
lean_dec_ref(v_proof_4789_);
lean_dec_ref(v_rhs_4788_);
lean_dec_ref(v_lhs_4787_);
return v___x_4811_;
}
}
else
{
lean_dec_ref(v___x_4809_);
lean_dec(v_generation_4790_);
lean_dec_ref(v_proof_4789_);
lean_dec_ref(v_rhs_4788_);
lean_dec_ref(v_lhs_4787_);
return v___x_4810_;
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v_generation_4790_);
lean_dec_ref(v_proof_4789_);
lean_dec_ref(v_rhs_4788_);
lean_dec_ref(v_lhs_4787_);
v_a_4816_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4802_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4802_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4824_, lean_object* v_rhs_4825_, lean_object* v_proof_4826_, lean_object* v_generation_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4824_, v_rhs_4825_, v_proof_4826_, v_generation_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec(v_a_4828_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4840_, lean_object* v_generation_4841_, lean_object* v_p_4842_, uint8_t v_isNeg_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = lean_box(0);
lean_inc(v_a_4853_);
lean_inc_ref(v_a_4852_);
lean_inc(v_a_4851_);
lean_inc_ref(v_a_4850_);
lean_inc(v_a_4849_);
lean_inc_ref(v_a_4848_);
lean_inc(v_a_4847_);
lean_inc_ref(v_a_4846_);
lean_inc(v_a_4845_);
lean_inc(v_a_4844_);
lean_inc_ref(v_p_4842_);
v___x_4856_ = lean_grind_internalize(v_p_4842_, v_generation_4841_, v___x_4855_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_dec_ref_known(v___x_4856_, 1);
if (v_isNeg_4843_ == 0)
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4848_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4859_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v___x_4859_ = l_Lean_Meta_mkEqTrue(v_proof_4840_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4861_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref_known(v___x_4859_, 1);
v___x_4861_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4842_, v_a_4858_, v_a_4860_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4861_;
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_dec(v_a_4858_);
lean_dec_ref(v_p_4842_);
v_a_4862_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4859_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4859_);
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
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
lean_dec_ref(v_p_4842_);
lean_dec_ref(v_proof_4840_);
v_a_4870_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4857_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4857_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
else
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4848_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; lean_object* v___x_4880_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref_known(v___x_4878_, 1);
v___x_4880_ = l_Lean_Meta_mkEqFalse(v_proof_4840_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref_known(v___x_4880_, 1);
v___x_4882_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4842_, v_a_4879_, v_a_4881_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4882_;
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v_a_4879_);
lean_dec_ref(v_p_4842_);
v_a_4883_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4880_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4880_);
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
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec_ref(v_p_4842_);
lean_dec_ref(v_proof_4840_);
v_a_4891_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4878_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4878_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4842_);
lean_dec_ref(v_proof_4840_);
return v___x_4856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4899_, lean_object* v_generation_4900_, lean_object* v_p_4901_, lean_object* v_isNeg_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
uint8_t v_isNeg_boxed_4914_; lean_object* v_res_4915_; 
v_isNeg_boxed_4914_ = lean_unbox(v_isNeg_4902_);
v_res_4915_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4899_, v_generation_4900_, v_p_4901_, v_isNeg_boxed_4914_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
lean_dec(v_a_4908_);
lean_dec_ref(v_a_4907_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec(v_a_4903_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4916_, lean_object* v_generation_4917_, lean_object* v_p_4918_, lean_object* v_lhs_4919_, lean_object* v_rhs_4920_, uint8_t v_isNeg_4921_, uint8_t v_isHEq_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
if (v_isNeg_4921_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_inc_ref(v_p_4918_);
v___x_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4934_, 0, v_p_4918_);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc(v_a_4923_);
lean_inc_ref(v___x_4934_);
lean_inc(v_generation_4917_);
lean_inc_ref(v_lhs_4919_);
v___x_4935_ = lean_grind_internalize(v_lhs_4919_, v_generation_4917_, v___x_4934_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4936_; 
lean_dec_ref_known(v___x_4935_, 1);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc(v_a_4923_);
lean_inc_ref(v_rhs_4920_);
v___x_4936_ = lean_grind_internalize(v_rhs_4920_, v_generation_4917_, v___x_4934_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
lean_dec_ref_known(v___x_4936_, 1);
v___x_4937_ = lean_box(0);
v___x_4938_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4918_, v___x_4937_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v___x_4939_; 
lean_dec_ref_known(v___x_4938_, 1);
v___x_4939_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4919_, v_rhs_4920_, v_proof_4916_, v_isHEq_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
return v___x_4939_;
}
else
{
lean_dec_ref(v_rhs_4920_);
lean_dec_ref(v_lhs_4919_);
lean_dec_ref(v_proof_4916_);
return v___x_4938_;
}
}
else
{
lean_dec_ref(v_rhs_4920_);
lean_dec_ref(v_lhs_4919_);
lean_dec_ref(v_p_4918_);
lean_dec_ref(v_proof_4916_);
return v___x_4936_;
}
}
else
{
lean_dec_ref_known(v___x_4934_, 1);
lean_dec_ref(v_rhs_4920_);
lean_dec_ref(v_lhs_4919_);
lean_dec_ref(v_p_4918_);
lean_dec(v_generation_4917_);
lean_dec_ref(v_proof_4916_);
return v___x_4935_;
}
}
else
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
lean_dec_ref(v_rhs_4920_);
lean_dec_ref(v_lhs_4919_);
v___x_4940_ = lean_box(0);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc_ref(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc(v_a_4923_);
lean_inc_ref(v_p_4918_);
v___x_4941_ = lean_grind_internalize(v_p_4918_, v_generation_4917_, v___x_4940_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref_known(v___x_4941_, 1);
v___x_4942_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4927_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___x_4942_, 1);
v___x_4944_ = l_Lean_Meta_mkEqFalse(v_proof_4916_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___x_4944_, 1);
v___x_4946_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4918_, v_a_4943_, v_a_4945_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_);
return v___x_4946_;
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec(v_a_4943_);
lean_dec_ref(v_p_4918_);
v_a_4947_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4944_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4944_);
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
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
lean_dec_ref(v_p_4918_);
lean_dec_ref(v_proof_4916_);
v_a_4955_ = lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4942_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4942_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
}
else
{
lean_dec_ref(v_p_4918_);
lean_dec_ref(v_proof_4916_);
return v___x_4941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4963_ = _args[0];
lean_object* v_generation_4964_ = _args[1];
lean_object* v_p_4965_ = _args[2];
lean_object* v_lhs_4966_ = _args[3];
lean_object* v_rhs_4967_ = _args[4];
lean_object* v_isNeg_4968_ = _args[5];
lean_object* v_isHEq_4969_ = _args[6];
lean_object* v_a_4970_ = _args[7];
lean_object* v_a_4971_ = _args[8];
lean_object* v_a_4972_ = _args[9];
lean_object* v_a_4973_ = _args[10];
lean_object* v_a_4974_ = _args[11];
lean_object* v_a_4975_ = _args[12];
lean_object* v_a_4976_ = _args[13];
lean_object* v_a_4977_ = _args[14];
lean_object* v_a_4978_ = _args[15];
lean_object* v_a_4979_ = _args[16];
lean_object* v_a_4980_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4981_; uint8_t v_isHEq_boxed_4982_; lean_object* v_res_4983_; 
v_isNeg_boxed_4981_ = lean_unbox(v_isNeg_4968_);
v_isHEq_boxed_4982_ = lean_unbox(v_isHEq_4969_);
v_res_4983_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4963_, v_generation_4964_, v_p_4965_, v_lhs_4966_, v_rhs_4967_, v_isNeg_boxed_4981_, v_isHEq_boxed_4982_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec(v_a_4971_);
lean_dec(v_a_4970_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4987_, lean_object* v_generation_4988_, lean_object* v_p_4989_, uint8_t v_isNeg_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v___x_5002_; 
lean_inc_ref(v_p_4989_);
v___x_5002_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4989_, v_a_4998_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5004_; uint8_t v___x_5005_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5003_);
lean_dec_ref_known(v___x_5002_, 1);
v___x_5004_ = l_Lean_Expr_cleanupAnnotations(v_a_5003_);
lean_dec(v_a_5003_);
v___x_5005_ = l_Lean_Expr_isApp(v___x_5004_);
if (v___x_5005_ == 0)
{
lean_object* v___x_5006_; 
lean_dec_ref(v___x_5004_);
v___x_5006_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5006_;
}
else
{
lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5007_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5004_);
v___x_5008_ = l_Lean_Expr_isApp(v___x_5007_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref(v___x_5007_);
lean_dec_ref(v___x_5004_);
v___x_5009_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5009_;
}
else
{
lean_object* v___x_5010_; uint8_t v___x_5011_; 
v___x_5010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5007_);
v___x_5011_ = l_Lean_Expr_isApp(v___x_5010_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref(v___x_5010_);
lean_dec_ref(v___x_5007_);
lean_dec_ref(v___x_5004_);
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5012_;
}
else
{
lean_object* v_arg_5013_; lean_object* v_arg_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; 
v_arg_5013_ = lean_ctor_get(v___x_5004_, 1);
lean_inc_ref(v_arg_5013_);
lean_dec_ref(v___x_5004_);
v_arg_5014_ = lean_ctor_get(v___x_5010_, 1);
lean_inc_ref(v_arg_5014_);
v___x_5015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5010_);
lean_dec_ref(v___x_5010_);
v___x_5016_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5017_ = l_Lean_Expr_isConstOf(v___x_5015_, v___x_5016_);
if (v___x_5017_ == 0)
{
uint8_t v___x_5018_; 
lean_dec_ref(v___x_5007_);
v___x_5018_ = l_Lean_Expr_isApp(v___x_5015_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
lean_dec_ref(v___x_5015_);
lean_dec_ref(v_arg_5014_);
lean_dec_ref(v_arg_5013_);
v___x_5019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5019_;
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; uint8_t v___x_5022_; 
v___x_5020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5015_);
lean_dec_ref(v___x_5015_);
v___x_5021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5022_ = l_Lean_Expr_isConstOf(v___x_5020_, v___x_5021_);
lean_dec_ref(v___x_5020_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; 
lean_dec_ref(v_arg_5014_);
lean_dec_ref(v_arg_5013_);
v___x_5023_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5023_;
}
else
{
lean_object* v___x_5024_; 
v___x_5024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4987_, v_generation_4988_, v_p_4989_, v_arg_5014_, v_arg_5013_, v_isNeg_4990_, v___x_5022_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5024_;
}
}
}
else
{
uint8_t v___x_5025_; 
lean_dec_ref(v___x_5015_);
v___x_5025_ = l_Lean_Expr_isProp(v_arg_5014_);
lean_dec_ref(v_arg_5014_);
if (v___x_5025_ == 0)
{
lean_object* v_arg_5026_; lean_object* v___x_5027_; 
v_arg_5026_ = lean_ctor_get(v___x_5007_, 1);
lean_inc_ref(v_arg_5026_);
lean_dec_ref(v___x_5007_);
v___x_5027_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4987_, v_generation_4988_, v_p_4989_, v_arg_5026_, v_arg_5013_, v_isNeg_4990_, v___x_5025_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5027_;
}
else
{
lean_object* v___x_5028_; 
lean_dec_ref(v_arg_5013_);
lean_dec_ref(v___x_5007_);
v___x_5028_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4987_, v_generation_4988_, v_p_4989_, v_isNeg_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
return v___x_5028_;
}
}
}
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec_ref(v_p_4989_);
lean_dec(v_generation_4988_);
lean_dec_ref(v_proof_4987_);
v_a_5029_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5002_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5002_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5037_, lean_object* v_generation_5038_, lean_object* v_p_5039_, lean_object* v_isNeg_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
uint8_t v_isNeg_boxed_5052_; lean_object* v_res_5053_; 
v_isNeg_boxed_5052_ = lean_unbox(v_isNeg_5040_);
v_res_5053_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5037_, v_generation_5038_, v_p_5039_, v_isNeg_boxed_5052_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec(v_a_5041_);
return v_res_5053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5062_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5063_ = l_Lean_Name_append(v___x_5062_, v___x_5061_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5064_, lean_object* v_proof_5065_, lean_object* v_generation_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5092_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___x_5109_; lean_object* v_toCold_5110_; lean_object* v_options_5111_; uint8_t v_hasTrace_5112_; 
lean_inc_ref(v_fact_5064_);
v___x_5109_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5064_, v_a_5067_);
lean_dec_ref(v___x_5109_);
v_toCold_5110_ = lean_ctor_get(v_a_5075_, 0);
v_options_5111_ = lean_ctor_get(v_toCold_5110_, 2);
v_hasTrace_5112_ = lean_ctor_get_uint8(v_options_5111_, sizeof(void*)*1);
if (v_hasTrace_5112_ == 0)
{
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
goto v___jp_5091_;
}
else
{
lean_object* v_inheritedTraceOptions_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; uint8_t v___x_5116_; 
v_inheritedTraceOptions_5113_ = lean_ctor_get(v_toCold_5110_, 11);
v___x_5114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5113_, v_options_5111_, v___x_5115_);
if (v___x_5116_ == 0)
{
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
goto v___jp_5091_;
}
else
{
lean_object* v___x_5117_; 
v___x_5117_ = l_Lean_Meta_Grind_updateLastTag(v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
lean_dec_ref_known(v___x_5117_, 1);
lean_inc_ref(v_fact_5064_);
v___x_5118_ = l_Lean_MessageData_ofExpr(v_fact_5064_);
v___x_5119_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5114_, v___x_5118_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_dec_ref_known(v___x_5119_, 1);
v___y_5092_ = v_a_5067_;
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
goto v___jp_5091_;
}
else
{
lean_dec(v_generation_5066_);
lean_dec_ref(v_proof_5065_);
lean_dec_ref(v_fact_5064_);
return v___x_5119_;
}
}
else
{
lean_dec(v_generation_5066_);
lean_dec_ref(v_proof_5065_);
lean_dec_ref(v_fact_5064_);
return v___x_5117_;
}
}
}
v___jp_5078_:
{
uint8_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5089_ = 0;
v___x_5090_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5065_, v_generation_5066_, v_fact_5064_, v___x_5089_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
return v___x_5090_;
}
v___jp_5091_:
{
lean_object* v___x_5102_; uint8_t v___x_5103_; 
v___x_5102_ = l_Lean_Expr_cleanupAnnotations(v_fact_5064_);
v___x_5103_ = l_Lean_Expr_isApp(v___x_5102_);
if (v___x_5103_ == 0)
{
lean_dec_ref(v___x_5102_);
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
goto v___jp_5078_;
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5102_);
v___x_5105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5106_ = l_Lean_Expr_isConstOf(v___x_5104_, v___x_5105_);
lean_dec_ref(v___x_5104_);
if (v___x_5106_ == 0)
{
lean_dec_ref(v___x_5102_);
v___y_5079_ = v___y_5092_;
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
goto v___jp_5078_;
}
else
{
lean_object* v_arg_5107_; lean_object* v___x_5108_; 
lean_dec_ref(v_fact_5064_);
v_arg_5107_ = lean_ctor_get(v___x_5102_, 1);
lean_inc_ref(v_arg_5107_);
lean_dec_ref(v___x_5102_);
v___x_5108_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5065_, v_generation_5066_, v_arg_5107_, v___x_5106_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_);
return v___x_5108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5120_, lean_object* v_proof_5121_, lean_object* v_generation_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5120_, v_proof_5121_, v_generation_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_);
lean_dec(v_a_5132_);
lean_dec_ref(v_a_5131_);
lean_dec(v_a_5130_);
lean_dec_ref(v_a_5129_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
lean_dec(v_a_5126_);
lean_dec_ref(v_a_5125_);
lean_dec(v_a_5124_);
lean_dec(v_a_5123_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_object* v_a_5150_; uint8_t v___x_5151_; 
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc(v_a_5150_);
lean_dec_ref_known(v___x_5149_, 1);
v___x_5151_ = lean_unbox(v_a_5150_);
lean_dec(v_a_5150_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5153_ = l_Lean_Core_checkSystem(v___x_5152_, v___y_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v___x_5154_; 
lean_dec_ref_known(v___x_5153_, 1);
v___x_5154_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5228_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5157_ = v___x_5154_;
v_isShared_5158_ = v_isSharedCheck_5228_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5154_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5228_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
if (lean_obj_tag(v_a_5155_) == 1)
{
lean_object* v_val_5159_; 
lean_del_object(v___x_5157_);
v_val_5159_ = lean_ctor_get(v_a_5155_, 0);
lean_inc(v_val_5159_);
lean_dec_ref_known(v_a_5155_, 1);
switch(lean_obj_tag(v_val_5159_))
{
case 0:
{
lean_object* v_lhs_5160_; lean_object* v_rhs_5161_; lean_object* v_proof_5162_; uint8_t v_isHEq_5163_; lean_object* v___x_5164_; 
v_lhs_5160_ = lean_ctor_get(v_val_5159_, 0);
lean_inc_ref(v_lhs_5160_);
v_rhs_5161_ = lean_ctor_get(v_val_5159_, 1);
lean_inc_ref(v_rhs_5161_);
v_proof_5162_ = lean_ctor_get(v_val_5159_, 2);
lean_inc_ref(v_proof_5162_);
v_isHEq_5163_ = lean_ctor_get_uint8(v_val_5159_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5159_, 3);
v___x_5164_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5160_, v_rhs_5161_, v_proof_5162_, v_isHEq_5163_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_dec_ref_known(v___x_5164_, 1);
goto _start;
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5173_; 
v_a_5166_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5168_ = v___x_5164_;
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5164_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
case 1:
{
lean_object* v_prop_5174_; lean_object* v_proof_5175_; lean_object* v_generation_5176_; lean_object* v___x_5177_; 
v_prop_5174_ = lean_ctor_get(v_val_5159_, 0);
lean_inc_ref(v_prop_5174_);
v_proof_5175_ = lean_ctor_get(v_val_5159_, 1);
lean_inc_ref(v_proof_5175_);
v_generation_5176_ = lean_ctor_get(v_val_5159_, 2);
lean_inc(v_generation_5176_);
lean_dec_ref_known(v_val_5159_, 3);
v___x_5177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5174_, v_proof_5175_, v_generation_5176_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_dec_ref_known(v___x_5177_, 1);
goto _start;
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
v_a_5179_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5177_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5177_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
case 2:
{
lean_object* v_e_5187_; lean_object* v___x_5188_; 
v_e_5187_ = lean_ctor_get(v_val_5159_, 0);
lean_inc_ref(v_e_5187_);
lean_dec_ref_known(v_val_5159_, 1);
v___x_5188_ = l_Lean_Meta_Grind_propagateUp(v_e_5187_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_dec_ref_known(v___x_5188_, 1);
goto _start;
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
v_a_5190_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5188_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5188_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
case 3:
{
lean_object* v_solverId_5198_; lean_object* v_lhs_5199_; lean_object* v_rhs_5200_; lean_object* v___x_5201_; 
v_solverId_5198_ = lean_ctor_get(v_val_5159_, 0);
lean_inc(v_solverId_5198_);
v_lhs_5199_ = lean_ctor_get(v_val_5159_, 1);
lean_inc_ref(v_lhs_5199_);
v_rhs_5200_ = lean_ctor_get(v_val_5159_, 2);
lean_inc_ref(v_rhs_5200_);
lean_dec_ref_known(v_val_5159_, 3);
v___x_5201_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5198_, v_lhs_5199_, v_rhs_5200_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
lean_dec(v_solverId_5198_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_dec_ref_known(v___x_5201_, 1);
goto _start;
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
v_a_5203_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5201_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5201_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
default: 
{
lean_object* v_solverId_5211_; lean_object* v_lhs_5212_; lean_object* v_rhs_5213_; lean_object* v___x_5214_; 
v_solverId_5211_ = lean_ctor_get(v_val_5159_, 0);
lean_inc(v_solverId_5211_);
v_lhs_5212_ = lean_ctor_get(v_val_5159_, 1);
lean_inc_ref(v_lhs_5212_);
v_rhs_5213_ = lean_ctor_get(v_val_5159_, 2);
lean_inc_ref(v_rhs_5213_);
lean_dec_ref_known(v_val_5159_, 3);
v___x_5214_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5211_, v_lhs_5212_, v_rhs_5213_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
lean_dec(v_solverId_5211_);
if (lean_obj_tag(v___x_5214_) == 0)
{
lean_dec_ref_known(v___x_5214_, 1);
goto _start;
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
v_a_5216_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5214_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5214_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5226_; 
lean_dec(v_a_5155_);
v___x_5224_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5158_ == 0)
{
lean_ctor_set(v___x_5157_, 0, v___x_5224_);
v___x_5226_ = v___x_5157_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5224_);
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
v_a_5229_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5154_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5154_);
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
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
v_a_5237_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5153_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5153_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5242_; 
if (v_isShared_5240_ == 0)
{
v___x_5242_ = v___x_5239_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
}
}
else
{
lean_object* v___x_5245_; 
v___x_5245_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5253_; 
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v___x_5245_, 0);
lean_dec(v_unused_5254_);
v___x_5247_ = v___x_5245_;
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
else
{
lean_dec(v___x_5245_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5253_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5248_ == 0)
{
lean_ctor_set(v___x_5247_, 0, v___x_5249_);
v___x_5251_ = v___x_5247_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
v_a_5255_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5245_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5245_);
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
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
v_a_5263_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5149_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5149_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec(v___y_5271_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = lean_box(0);
v___x_5295_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
lean_dec(v_a_5292_);
lean_dec_ref(v_a_5291_);
lean_dec(v_a_5290_);
lean_dec_ref(v_a_5289_);
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_a_5284_);
lean_dec(v_a_5283_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5308_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5298_ = v___x_5295_;
v_isShared_5299_ = v_isSharedCheck_5308_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5295_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5308_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v_fst_5300_; 
v_fst_5300_ = lean_ctor_get(v_a_5296_, 0);
lean_inc(v_fst_5300_);
lean_dec(v_a_5296_);
if (lean_obj_tag(v_fst_5300_) == 0)
{
lean_object* v___x_5302_; 
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 0, v___x_5294_);
v___x_5302_ = v___x_5298_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5294_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
else
{
lean_object* v_val_5304_; lean_object* v___x_5306_; 
v_val_5304_ = lean_ctor_get(v_fst_5300_, 0);
lean_inc(v_val_5304_);
lean_dec_ref_known(v_fst_5300_, 1);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 0, v_val_5304_);
v___x_5306_ = v___x_5298_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_val_5304_);
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
else
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5316_; 
v_a_5309_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5316_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5316_ == 0)
{
v___x_5311_ = v___x_5295_;
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v___x_5295_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5314_; 
if (v_isShared_5312_ == 0)
{
v___x_5314_ = v___x_5311_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
return v___x_5314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = lean_grind_process_to_do(v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5329_, lean_object* v_a_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v___x_5342_; 
v___x_5342_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5343_, lean_object* v_a_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5343_, v_a_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec(v___y_5345_);
lean_dec_ref(v_a_5344_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5357_, lean_object* v_proof_5358_, lean_object* v_generation_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_){
_start:
{
uint8_t v___x_5371_; 
v___x_5371_ = l_Lean_Expr_isTrue(v_fact_5357_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
v___x_5372_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5360_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5403_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5375_ = v___x_5372_;
v_isShared_5376_ = v_isSharedCheck_5403_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5372_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5403_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
uint8_t v___x_5377_; 
v___x_5377_ = lean_unbox(v_a_5373_);
lean_dec(v_a_5373_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; 
lean_del_object(v___x_5375_);
lean_inc(v_a_5369_);
lean_inc_ref(v_a_5368_);
lean_inc(v_a_5367_);
lean_inc_ref(v_a_5366_);
lean_inc(v_a_5365_);
lean_inc_ref(v_a_5364_);
lean_inc(v_a_5363_);
lean_inc_ref(v_a_5362_);
lean_inc(v_a_5361_);
lean_inc(v_a_5360_);
v___x_5378_ = lean_grind_process_to_do(v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_);
if (lean_obj_tag(v___x_5378_) == 0)
{
lean_object* v___x_5379_; 
lean_dec_ref_known(v___x_5378_, 1);
v___x_5379_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5360_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5390_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5382_ = v___x_5379_;
v_isShared_5383_ = v_isSharedCheck_5390_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5379_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5390_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
uint8_t v___x_5384_; 
v___x_5384_ = lean_unbox(v_a_5380_);
lean_dec(v_a_5380_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; 
lean_del_object(v___x_5382_);
v___x_5385_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5357_, v_proof_5358_, v_generation_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_);
return v___x_5385_;
}
else
{
lean_object* v___x_5386_; lean_object* v___x_5388_; 
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
v___x_5386_ = lean_box(0);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 0, v___x_5386_);
v___x_5388_ = v___x_5382_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5386_);
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
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5398_; 
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
v_a_5391_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5393_ = v___x_5379_;
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5379_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
lean_object* v___x_5396_; 
if (v_isShared_5394_ == 0)
{
v___x_5396_ = v___x_5393_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
}
else
{
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
return v___x_5378_;
}
}
else
{
lean_object* v___x_5399_; lean_object* v___x_5401_; 
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
v___x_5399_ = lean_box(0);
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v___x_5399_);
v___x_5401_ = v___x_5375_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5399_);
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
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
v_a_5404_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5372_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5372_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
else
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
lean_dec(v_generation_5359_);
lean_dec_ref(v_proof_5358_);
lean_dec_ref(v_fact_5357_);
v___x_5412_ = lean_box(0);
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5412_);
return v___x_5413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5414_, lean_object* v_proof_5415_, lean_object* v_generation_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Lean_Meta_Grind_add(v_fact_5414_, v_proof_5415_, v_generation_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_);
lean_dec(v_a_5426_);
lean_dec_ref(v_a_5425_);
lean_dec(v_a_5424_);
lean_dec_ref(v_a_5423_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec(v_a_5417_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5429_, lean_object* v_generation_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v___x_5442_; 
lean_inc(v_fvarId_5429_);
v___x_5442_ = l_Lean_FVarId_getType___redArg(v_fvarId_5429_, v_a_5437_, v_a_5439_, v_a_5440_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v___x_5444_ = l_Lean_mkFVar(v_fvarId_5429_);
v___x_5445_ = l_Lean_Meta_Grind_add(v_a_5443_, v___x_5444_, v_generation_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_);
return v___x_5445_;
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec(v_generation_5430_);
lean_dec(v_fvarId_5429_);
v_a_5446_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5442_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5442_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5454_, lean_object* v_generation_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5454_, v_generation_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_a_5460_);
lean_dec(v_a_5459_);
lean_dec_ref(v_a_5458_);
lean_dec(v_a_5457_);
lean_dec(v_a_5456_);
return v_res_5467_;
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
