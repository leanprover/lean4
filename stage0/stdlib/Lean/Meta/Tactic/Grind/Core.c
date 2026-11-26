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
size_t v_x_23182__boxed_357_; lean_object* v_res_358_; 
v_x_23182__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_23182__boxed_357_, v_x_356_);
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
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v___x_447_; 
v_head_399_ = lean_ctor_get(v_as_x27_385_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_385_, 1);
v___x_401_ = lean_box(0);
v___x_447_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_399_);
if (v___x_447_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v___x_449_; 
lean_inc(v_head_399_);
v___x_449_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_399_, v___y_387_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; uint8_t v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_unbox(v_a_450_);
lean_dec(v_a_450_);
if (v___x_451_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_toCold_453_; lean_object* v_options_454_; uint8_t v_hasTrace_455_; 
v_toCold_453_ = lean_ctor_get(v___y_395_, 0);
v_options_454_ = lean_ctor_get(v_toCold_453_, 2);
v_hasTrace_455_ = lean_ctor_get_uint8(v_options_454_, sizeof(void*)*1);
if (v_hasTrace_455_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_inheritedTraceOptions_456_ = lean_ctor_get(v_toCold_453_, 11);
v___x_457_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_458_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_456_, v_options_454_, v___x_458_);
if (v___x_459_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Grind_updateLastTag(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref_known(v___x_460_, 1);
v___x_461_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_462_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_457_, v___x_463_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
return v___x_464_;
}
}
else
{
return v___x_460_;
}
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_449_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_449_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toGoalState_405_; lean_object* v_mvarId_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_446_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toGoalState_405_ = lean_ctor_get(v___x_404_, 0);
v_mvarId_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_446_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_446_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_mvarId_406_);
lean_inc(v_toGoalState_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_446_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_nextDeclIdx_410_; lean_object* v_enodeMap_411_; lean_object* v_exprs_412_; lean_object* v_parents_413_; lean_object* v_congrTable_414_; lean_object* v_appMap_415_; lean_object* v_indicesFound_416_; lean_object* v_toProcess_417_; lean_object* v_internalizing_418_; uint8_t v_inconsistent_419_; lean_object* v_nextIdx_420_; lean_object* v_newRawFacts_421_; lean_object* v_facts_422_; lean_object* v_extThms_423_; lean_object* v_ematch_424_; lean_object* v_inj_425_; lean_object* v_split_426_; lean_object* v_clean_427_; lean_object* v_sstates_428_; lean_object* v_goalStack_429_; uint64_t v_introBase_430_; lean_object* v_numIntros_431_; lean_object* v_relevance_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_445_; 
v_nextDeclIdx_410_ = lean_ctor_get(v_toGoalState_405_, 0);
v_enodeMap_411_ = lean_ctor_get(v_toGoalState_405_, 1);
v_exprs_412_ = lean_ctor_get(v_toGoalState_405_, 2);
v_parents_413_ = lean_ctor_get(v_toGoalState_405_, 3);
v_congrTable_414_ = lean_ctor_get(v_toGoalState_405_, 4);
v_appMap_415_ = lean_ctor_get(v_toGoalState_405_, 5);
v_indicesFound_416_ = lean_ctor_get(v_toGoalState_405_, 6);
v_toProcess_417_ = lean_ctor_get(v_toGoalState_405_, 7);
v_internalizing_418_ = lean_ctor_get(v_toGoalState_405_, 8);
v_inconsistent_419_ = lean_ctor_get_uint8(v_toGoalState_405_, sizeof(void*)*21 + 8);
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
v_introBase_430_ = lean_ctor_get_uint64(v_toGoalState_405_, sizeof(void*)*21);
v_numIntros_431_ = lean_ctor_get(v_toGoalState_405_, 19);
v_relevance_432_ = lean_ctor_get(v_toGoalState_405_, 20);
v_isSharedCheck_445_ = !lean_is_exclusive(v_toGoalState_405_);
if (v_isSharedCheck_445_ == 0)
{
v___x_434_ = v_toGoalState_405_;
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_relevance_432_);
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
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_445_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_head_399_);
v___x_436_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_411_, v_congrTable_414_, v_head_399_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_nextDeclIdx_410_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_enodeMap_411_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_exprs_412_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_parents_413_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_appMap_415_);
lean_ctor_set(v_reuseFailAlloc_444_, 6, v_indicesFound_416_);
lean_ctor_set(v_reuseFailAlloc_444_, 7, v_toProcess_417_);
lean_ctor_set(v_reuseFailAlloc_444_, 8, v_internalizing_418_);
lean_ctor_set(v_reuseFailAlloc_444_, 9, v_nextIdx_420_);
lean_ctor_set(v_reuseFailAlloc_444_, 10, v_newRawFacts_421_);
lean_ctor_set(v_reuseFailAlloc_444_, 11, v_facts_422_);
lean_ctor_set(v_reuseFailAlloc_444_, 12, v_extThms_423_);
lean_ctor_set(v_reuseFailAlloc_444_, 13, v_ematch_424_);
lean_ctor_set(v_reuseFailAlloc_444_, 14, v_inj_425_);
lean_ctor_set(v_reuseFailAlloc_444_, 15, v_split_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 16, v_clean_427_);
lean_ctor_set(v_reuseFailAlloc_444_, 17, v_sstates_428_);
lean_ctor_set(v_reuseFailAlloc_444_, 18, v_goalStack_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 19, v_numIntros_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 20, v_relevance_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_444_, sizeof(void*)*21 + 8, v_inconsistent_419_);
lean_ctor_set_uint64(v_reuseFailAlloc_444_, sizeof(void*)*21, v_introBase_430_);
v___x_438_ = v_reuseFailAlloc_444_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_438_);
v___x_440_ = v___x_408_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_mvarId_406_);
v___x_440_ = v_reuseFailAlloc_443_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; 
v___x_441_ = lean_st_ref_put(v___y_403_, v___x_440_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_473_, v_b_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v_as_x27_473_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_getParents___redArg(v_root_487_, v_a_488_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_500_);
v___x_502_ = lean_box(0);
v___x_503_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_501_, v___x_502_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v___x_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v___x_503_, 0);
lean_dec(v_unused_511_);
v___x_505_ = v___x_503_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_dec(v___x_503_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_a_500_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_500_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_a_500_);
v_a_512_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_503_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_503_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_root_520_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_533_, lean_object* v_00_u03b2_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_533_, v_x_535_, v_x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_538_, lean_object* v_00_u03b2_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_538_, v_00_u03b2_539_, v_x_540_, v_x_541_);
lean_dec_ref(v___x_538_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_543_, v_msg_544_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_557_, lean_object* v_msg_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_557_, v_msg_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec(v___y_559_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_571_, lean_object* v_as_x27_572_, lean_object* v_b_573_, lean_object* v_a_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_572_, v_b_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_587_, lean_object* v_as_x27_588_, lean_object* v_b_589_, lean_object* v_a_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_587_, v_as_x27_588_, v_b_589_, v_a_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec(v___y_591_);
lean_dec(v_as_x27_588_);
lean_dec(v_as_587_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_603_, lean_object* v_00_u03b2_604_, lean_object* v_x_605_, size_t v_x_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_603_, v_x_605_, v_x_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_609_, lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
size_t v_x_23642__boxed_614_; lean_object* v_res_615_; 
v_x_23642__boxed_614_ = lean_unbox_usize(v_x_612_);
lean_dec(v_x_612_);
v_res_615_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_609_, v_00_u03b2_610_, v_x_611_, v_x_23642__boxed_614_, v_x_613_);
lean_dec_ref(v___x_609_);
return v_res_615_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_as_x27_619_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_b_620_);
return v___x_632_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_635_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; uint8_t v___x_649_; 
v_head_633_ = lean_ctor_get(v_as_x27_619_, 0);
v_tail_634_ = lean_ctor_get(v_as_x27_619_, 1);
v___x_635_ = lean_box(0);
v___x_649_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_633_);
if (v___x_649_ == 0)
{
v_as_x27_619_ = v_tail_634_;
v_b_620_ = v___x_635_;
goto _start;
}
else
{
lean_object* v___x_651_; 
lean_inc(v_head_633_);
v___x_651_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_633_, v___y_621_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = lean_unbox(v_a_652_);
lean_dec(v_a_652_);
if (v___x_653_ == 0)
{
v_as_x27_619_ = v_tail_634_;
v_b_620_ = v___x_635_;
goto _start;
}
else
{
lean_object* v_toCold_655_; lean_object* v_options_656_; uint8_t v_hasTrace_657_; 
v_toCold_655_ = lean_ctor_get(v___y_629_, 0);
v_options_656_ = lean_ctor_get(v_toCold_655_, 2);
v_hasTrace_657_ = lean_ctor_get_uint8(v_options_656_, sizeof(void*)*1);
if (v_hasTrace_657_ == 0)
{
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
v___y_646_ = v___y_630_;
goto v___jp_636_;
}
else
{
lean_object* v_inheritedTraceOptions_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_inheritedTraceOptions_658_ = lean_ctor_get(v_toCold_655_, 11);
v___x_659_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_660_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_658_, v_options_656_, v___x_660_);
if (v___x_661_ == 0)
{
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
v___y_646_ = v___y_630_;
goto v___jp_636_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_updateLastTag(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref_known(v___x_662_, 1);
v___x_663_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_633_);
v___x_664_ = l_Lean_MessageData_ofExpr(v_head_633_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_659_, v___x_665_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_dec_ref_known(v___x_666_, 1);
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
v___y_645_ = v___y_629_;
v___y_646_ = v___y_630_;
goto v___jp_636_;
}
else
{
return v___x_666_;
}
}
else
{
return v___x_662_;
}
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_651_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_651_);
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
v___jp_636_:
{
lean_object* v___x_647_; 
lean_inc(v_head_633_);
v___x_647_ = l_Lean_Meta_Grind_addCongrTable(v_head_633_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v_as_x27_619_ = v_tail_634_;
v_b_620_ = v___x_635_;
goto _start;
}
else
{
return v___x_647_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2031_, lean_object* v_as_2032_, size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_a_2048_; uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_b_2035_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v_a_2055_; 
v___x_2054_ = lean_box(0);
v_a_2055_ = lean_array_uget_borrowed(v_as_2032_, v_i_2034_);
if (lean_obj_tag(v_a_2055_) == 6)
{
lean_object* v_binderType_2056_; lean_object* v_body_2057_; lean_object* v___x_2058_; 
v_binderType_2056_ = lean_ctor_get(v_a_2055_, 1);
v_body_2057_ = lean_ctor_get(v_a_2055_, 2);
lean_inc_ref(v_binderType_2056_);
v___x_2058_ = l_Lean_Meta_getLevel(v_binderType_2056_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_a_2059_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_inc_ref(v___x_2062_);
v___x_2063_ = l_Lean_mkConst(v___x_2060_, v___x_2062_);
lean_inc_ref(v_binderType_2056_);
v___x_2064_ = l_Lean_Expr_app___override(v___x_2063_, v_binderType_2056_);
v___x_2065_ = lean_box(0);
v___x_2066_ = l_Lean_Meta_synthInstance_x3f(v___x_2064_, v___x_2065_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___x_2131_; 
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_a_2067_, 1);
v___x_2131_ = l_Lean_Expr_hasLooseBVars(v_body_2057_);
if (v___x_2131_ == 0)
{
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
v___y_2077_ = v___y_2043_;
v___y_2078_ = v___y_2044_;
v___y_2079_ = v___y_2045_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2062_);
v___x_2133_ = l_Lean_mkConst(v___x_2132_, v___x_2062_);
lean_inc_ref(v_binderType_2056_);
v___x_2134_ = l_Lean_Expr_app___override(v___x_2133_, v_binderType_2056_);
v___x_2135_ = l_Lean_Meta_synthInstance_x3f(v___x_2134_, v___x_2065_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
if (lean_obj_tag(v_a_2136_) == 0)
{
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
lean_dec_ref_known(v_a_2136_, 1);
v___y_2070_ = v___y_2036_;
v___y_2071_ = v___y_2037_;
v___y_2072_ = v___y_2038_;
v___y_2073_ = v___y_2039_;
v___y_2074_ = v___y_2040_;
v___y_2075_ = v___y_2041_;
v___y_2076_ = v___y_2042_;
v___y_2077_ = v___y_2043_;
v___y_2078_ = v___y_2044_;
v___y_2079_ = v___y_2045_;
goto v___jp_2069_;
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
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
v___jp_2069_:
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2031_, v_binderType_2056_);
if (lean_obj_tag(v___x_2080_) == 1)
{
lean_object* v_val_2081_; 
v_val_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v___x_2080_, 1);
if (lean_obj_tag(v_val_2081_) == 6)
{
lean_object* v_body_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_body_2082_ = lean_ctor_get(v_val_2081_, 2);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2084_ = l_Lean_mkConst(v___x_2083_, v___x_2062_);
lean_inc_ref(v_binderType_2056_);
v___x_2085_ = l_Lean_mkAppB(v___x_2084_, v_binderType_2056_, v_val_2068_);
v___x_2086_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2085_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_expr_instantiate1(v_body_2057_, v_a_2087_);
v___x_2089_ = lean_expr_instantiate1(v_body_2082_, v_a_2087_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v___y_2075_);
lean_inc_ref(v___y_2074_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v_a_2055_);
v___x_2090_ = lean_grind_mk_eq_proof(v_a_2055_, v_val_2081_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Meta_mkCongrFun(v_a_2091_, v_a_2087_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_Meta_mkEq(v___x_2088_, v___x_2089_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_mkExpectedPropHint(v_a_2093_, v_a_2095_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = l_Lean_Meta_Grind_pushNewFact(v___x_2096_, v___x_2097_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
return v___x_2098_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2093_);
v_a_2099_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2094_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2094_);
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
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
v_a_2107_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2092_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2092_);
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
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v_a_2087_);
v_a_2115_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2090_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2090_);
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
lean_dec_ref_known(v_val_2081_, 3);
v_a_2123_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2086_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2086_);
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
lean_dec(v_val_2081_);
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_dec(v___x_2080_);
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
}
else
{
lean_dec(v_a_2067_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref_known(v___x_2062_, 2);
v_a_2145_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2066_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2066_);
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
v_a_2153_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2058_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2058_);
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
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
v___jp_2047_:
{
size_t v___x_2049_; size_t v___x_2050_; 
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2034_, v___x_2049_);
v_i_2034_ = v___x_2050_;
v_b_2035_ = v_a_2048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object* v_lams_u2082_2161_, lean_object* v_as_2162_, lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_b_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
size_t v_sz_boxed_2177_; size_t v_i_boxed_2178_; lean_object* v_res_2179_; 
v_sz_boxed_2177_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2178_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2161_, v_as_2162_, v_sz_boxed_2177_, v_i_boxed_2178_, v_b_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v_as_2162_);
lean_dec_ref(v_lams_u2082_2161_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2180_, lean_object* v_lams_u2082_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = lean_array_get_size(v_lams_u2081_2180_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_nat_dec_eq(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = lean_array_get_size(v_lams_u2082_2181_);
v___x_2200_ = lean_nat_dec_eq(v___x_2199_, v___x_2197_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; size_t v_sz_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = lean_box(0);
v_sz_2202_ = lean_array_size(v_lams_u2081_2180_);
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2181_, v_lams_u2081_2180_, v_sz_2202_, v___x_2203_, v___x_2201_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2204_, 0);
lean_dec(v_unused_2212_);
v___x_2206_ = v___x_2204_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v___x_2204_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2201_);
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2201_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
return v___x_2204_;
}
}
else
{
goto v___jp_2193_;
}
}
else
{
goto v___jp_2193_;
}
v___jp_2193_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2213_, lean_object* v_lams_u2082_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2213_, v_lams_u2082_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_lams_u2082_2214_);
lean_dec_ref(v_lams_u2081_2213_);
return v_res_2226_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2227_){
_start:
{
uint8_t v___x_2228_; 
v___x_2228_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2229_){
_start:
{
uint8_t v_res_2230_; lean_object* v_r_2231_; 
v_res_2230_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2229_);
lean_dec_ref(v_x_2229_);
v_r_2231_ = lean_box(v_res_2230_);
return v_r_2231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2232_, lean_object* v_x_2233_){
_start:
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_){
_start:
{
uint8_t v_res_2237_; lean_object* v_r_2238_; 
v_res_2237_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2235_, v_x_2236_);
lean_dec_ref(v_x_2236_);
v_r_2238_ = lean_box(v_res_2237_);
return v_r_2238_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2239_, lean_object* v_v_2240_, lean_object* v_i_2241_){
_start:
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = lean_array_get_size(v_xs_2239_);
v___x_2243_ = lean_nat_dec_lt(v_i_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec(v_i_2241_);
v___x_2244_ = lean_box(0);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; uint8_t v___x_2248_; 
v___x_2245_ = lean_array_fget_borrowed(v_xs_2239_, v_i_2241_);
v___x_2246_ = lean_ptr_addr(v___x_2245_);
v___x_2247_ = lean_ptr_addr(v_v_2240_);
v___x_2248_ = lean_usize_dec_eq(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v_i_2241_, v___x_2249_);
lean_dec(v_i_2241_);
v_i_2241_ = v___x_2250_;
goto _start;
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_i_2241_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2253_, lean_object* v_v_2254_, lean_object* v_i_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2253_, v_v_2254_, v_i_2255_);
lean_dec_ref(v_v_2254_);
lean_dec_ref(v_xs_2253_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2257_, lean_object* v_v_2258_){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2257_, v_v_2258_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2261_, lean_object* v_v_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2261_, v_v_2262_);
lean_dec_ref(v_v_2262_);
lean_dec_ref(v_xs_2261_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2264_, size_t v_x_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2264_) == 0)
{
lean_object* v_es_2267_; lean_object* v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; lean_object* v_j_2271_; lean_object* v_entry_2272_; 
v_es_2267_ = lean_ctor_get(v_x_2264_, 0);
v___x_2268_ = lean_box(2);
v___x_2269_ = ((size_t)31ULL);
v___x_2270_ = lean_usize_land(v_x_2265_, v___x_2269_);
v_j_2271_ = lean_usize_to_nat(v___x_2270_);
v_entry_2272_ = lean_array_get(v___x_2268_, v_es_2267_, v_j_2271_);
switch(lean_obj_tag(v_entry_2272_))
{
case 0:
{
lean_object* v_key_2273_; size_t v___x_2274_; size_t v___x_2275_; uint8_t v___x_2276_; 
v_key_2273_ = lean_ctor_get(v_entry_2272_, 0);
lean_inc(v_key_2273_);
lean_dec_ref_known(v_entry_2272_, 2);
v___x_2274_ = lean_ptr_addr(v_x_2266_);
v___x_2275_ = lean_ptr_addr(v_key_2273_);
lean_dec(v_key_2273_);
v___x_2276_ = lean_usize_dec_eq(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_dec(v_j_2271_);
return v_x_2264_;
}
else
{
lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2284_; 
lean_inc_ref(v_es_2267_);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_x_2264_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v_x_2264_, 0);
lean_dec(v_unused_2285_);
v___x_2278_ = v_x_2264_;
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
else
{
lean_dec(v_x_2264_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2284_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_array_set(v_es_2267_, v_j_2271_, v___x_2268_);
lean_dec(v_j_2271_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
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
}
case 1:
{
lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2320_; 
lean_inc_ref(v_es_2267_);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_x_2264_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v_x_2264_, 0);
lean_dec(v_unused_2321_);
v___x_2287_ = v_x_2264_;
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
else
{
lean_dec(v_x_2264_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2320_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v_node_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2319_; 
v_node_2289_ = lean_ctor_get(v_entry_2272_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_entry_2272_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2291_ = v_entry_2272_;
v_isShared_2292_ = v_isSharedCheck_2319_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_node_2289_);
lean_dec(v_entry_2272_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2319_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
size_t v___x_2293_; lean_object* v_entries_2294_; size_t v___x_2295_; lean_object* v_newNode_2296_; lean_object* v___x_2297_; 
v___x_2293_ = ((size_t)5ULL);
v_entries_2294_ = lean_array_set(v_es_2267_, v_j_2271_, v___x_2268_);
v___x_2295_ = lean_usize_shift_right(v_x_2265_, v___x_2293_);
v_newNode_2296_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2289_, v___x_2295_, v_x_2266_);
lean_inc_ref(v_newNode_2296_);
v___x_2297_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v___x_2299_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_newNode_2296_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_newNode_2296_);
v___x_2299_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_array_set(v_entries_2294_, v_j_2271_, v___x_2299_);
lean_dec(v_j_2271_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2300_);
v___x_2302_ = v___x_2287_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v_val_2305_; lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_newNode_2296_);
lean_del_object(v___x_2291_);
v_val_2305_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2297_, 1);
v_fst_2306_ = lean_ctor_get(v_val_2305_, 0);
v_snd_2307_ = lean_ctor_get(v_val_2305_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_val_2305_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2309_ = v_val_2305_;
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snd_2307_);
lean_inc(v_fst_2306_);
lean_dec(v_val_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_fst_2306_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_snd_2307_);
v___x_2312_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_array_set(v_entries_2294_, v_j_2271_, v___x_2312_);
lean_dec(v_j_2271_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2313_);
v___x_2315_ = v___x_2287_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2271_);
return v_x_2264_;
}
}
}
else
{
lean_object* v_ks_2322_; lean_object* v_vs_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_ks_2322_ = lean_ctor_get(v_x_2264_, 0);
v_vs_2323_ = lean_ctor_get(v_x_2264_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2264_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2325_ = v_x_2264_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_vs_2323_);
lean_inc(v_ks_2322_);
lean_dec(v_x_2264_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2322_, v_x_2266_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v___x_2329_; 
if (v_isShared_2326_ == 0)
{
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_ks_2322_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_vs_2323_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
else
{
lean_object* v_val_2331_; lean_object* v_keys_x27_2332_; lean_object* v_vals_x27_2333_; lean_object* v___x_2335_; 
v_val_2331_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_n(v_val_2331_, 2);
lean_dec_ref_known(v___x_2327_, 1);
v_keys_x27_2332_ = l_Array_eraseIdx___redArg(v_ks_2322_, v_val_2331_);
v_vals_x27_2333_ = l_Array_eraseIdx___redArg(v_vs_2323_, v_val_2331_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_vals_x27_2333_);
lean_ctor_set(v___x_2325_, 0, v_keys_x27_2332_);
v___x_2335_ = v___x_2325_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_keys_x27_2332_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_vals_x27_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v_x_19769__boxed_2341_; lean_object* v_res_2342_; 
v_x_19769__boxed_2341_ = lean_unbox_usize(v_x_2339_);
lean_dec(v_x_2339_);
v_res_2342_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2338_, v_x_19769__boxed_2341_, v_x_2340_);
lean_dec_ref(v_x_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
size_t v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; uint64_t v___x_2348_; size_t v_h_2349_; lean_object* v___x_2350_; 
v___x_2345_ = lean_ptr_addr(v_x_2344_);
v___x_2346_ = ((size_t)3ULL);
v___x_2347_ = lean_usize_shift_right(v___x_2345_, v___x_2346_);
v___x_2348_ = lean_usize_to_uint64(v___x_2347_);
v_h_2349_ = lean_uint64_to_usize(v___x_2348_);
v___x_2350_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2343_, v_h_2349_, v_x_2344_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2351_, v_x_2352_);
lean_dec_ref(v_x_2352_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
if (lean_obj_tag(v_as_2354_) == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
else
{
lean_object* v_head_2368_; lean_object* v_tail_2369_; lean_object* v___x_2370_; 
v_head_2368_ = lean_ctor_get(v_as_2354_, 0);
lean_inc(v_head_2368_);
v_tail_2369_ = lean_ctor_get(v_as_2354_, 1);
lean_inc(v_tail_2369_);
lean_dec_ref_known(v_as_2354_, 2);
v___x_2370_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2368_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_dec_ref_known(v___x_2370_, 1);
v_as_2354_ = v_tail_2369_;
goto _start;
}
else
{
lean_dec(v_tail_2369_);
return v___x_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec(v___y_2373_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2385_, lean_object* v_vals_2386_, lean_object* v_i_2387_, lean_object* v_k_2388_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = lean_array_get_size(v_keys_2385_);
v___x_2390_ = lean_nat_dec_lt(v_i_2387_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_dec(v_i_2387_);
v___x_2391_ = lean_box(0);
return v___x_2391_;
}
else
{
lean_object* v_k_x27_2392_; size_t v___x_2393_; size_t v___x_2394_; uint8_t v___x_2395_; 
v_k_x27_2392_ = lean_array_fget_borrowed(v_keys_2385_, v_i_2387_);
v___x_2393_ = lean_ptr_addr(v_k_2388_);
v___x_2394_ = lean_ptr_addr(v_k_x27_2392_);
v___x_2395_ = lean_usize_dec_eq(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_unsigned_to_nat(1u);
v___x_2397_ = lean_nat_add(v_i_2387_, v___x_2396_);
lean_dec(v_i_2387_);
v_i_2387_ = v___x_2397_;
goto _start;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_array_fget_borrowed(v_vals_2386_, v_i_2387_);
lean_dec(v_i_2387_);
lean_inc(v___x_2399_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2401_, lean_object* v_vals_2402_, lean_object* v_i_2403_, lean_object* v_k_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2401_, v_vals_2402_, v_i_2403_, v_k_2404_);
lean_dec_ref(v_k_2404_);
lean_dec_ref(v_vals_2402_);
lean_dec_ref(v_keys_2401_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2406_, size_t v_x_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_object* v_es_2409_; lean_object* v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; lean_object* v_j_2413_; lean_object* v___x_2414_; 
v_es_2409_ = lean_ctor_get(v_x_2406_, 0);
v___x_2410_ = lean_box(2);
v___x_2411_ = ((size_t)31ULL);
v___x_2412_ = lean_usize_land(v_x_2407_, v___x_2411_);
v_j_2413_ = lean_usize_to_nat(v___x_2412_);
v___x_2414_ = lean_array_get_borrowed(v___x_2410_, v_es_2409_, v_j_2413_);
lean_dec(v_j_2413_);
switch(lean_obj_tag(v___x_2414_))
{
case 0:
{
lean_object* v_key_2415_; lean_object* v_val_2416_; size_t v___x_2417_; size_t v___x_2418_; uint8_t v___x_2419_; 
v_key_2415_ = lean_ctor_get(v___x_2414_, 0);
v_val_2416_ = lean_ctor_get(v___x_2414_, 1);
v___x_2417_ = lean_ptr_addr(v_x_2408_);
v___x_2418_ = lean_ptr_addr(v_key_2415_);
v___x_2419_ = lean_usize_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; 
lean_inc(v_val_2416_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_val_2416_);
return v___x_2421_;
}
}
case 1:
{
lean_object* v_node_2422_; size_t v___x_2423_; size_t v___x_2424_; 
v_node_2422_ = lean_ctor_get(v___x_2414_, 0);
v___x_2423_ = ((size_t)5ULL);
v___x_2424_ = lean_usize_shift_right(v_x_2407_, v___x_2423_);
v_x_2406_ = v_node_2422_;
v_x_2407_ = v___x_2424_;
goto _start;
}
default: 
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
}
}
else
{
lean_object* v_ks_2427_; lean_object* v_vs_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_ks_2427_ = lean_ctor_get(v_x_2406_, 0);
v_vs_2428_ = lean_ctor_get(v_x_2406_, 1);
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2427_, v_vs_2428_, v___x_2429_, v_x_2408_);
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2431_, lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
size_t v_x_19994__boxed_2434_; lean_object* v_res_2435_; 
v_x_19994__boxed_2434_ = lean_unbox_usize(v_x_2432_);
lean_dec(v_x_2432_);
v_res_2435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2431_, v_x_19994__boxed_2434_, v_x_2433_);
lean_dec_ref(v_x_2433_);
lean_dec_ref(v_x_2431_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2436_, lean_object* v_x_2437_){
_start:
{
size_t v___x_2438_; size_t v___x_2439_; size_t v___x_2440_; uint64_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2438_ = lean_ptr_addr(v_x_2437_);
v___x_2439_ = ((size_t)3ULL);
v___x_2440_ = lean_usize_shift_right(v___x_2438_, v___x_2439_);
v___x_2441_ = lean_usize_to_uint64(v___x_2440_);
v___x_2442_ = lean_uint64_to_usize(v___x_2441_);
v___x_2443_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2436_, v___x_2442_, v_x_2437_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2444_, v_x_2445_);
lean_dec_ref(v_x_2445_);
lean_dec_ref(v_x_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
if (lean_obj_tag(v_as_x27_2447_) == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_b_2448_);
return v___x_2460_;
}
else
{
lean_object* v_head_2461_; lean_object* v_tail_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_toGoalState_2465_; lean_object* v_ematch_2466_; lean_object* v_delayedThmInsts_2467_; lean_object* v___x_2468_; 
v_head_2461_ = lean_ctor_get(v_as_x27_2447_, 0);
v_tail_2462_ = lean_ctor_get(v_as_x27_2447_, 1);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_st_ref_get(v___y_2449_);
v_toGoalState_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_toGoalState_2465_);
lean_dec(v___x_2464_);
v_ematch_2466_ = lean_ctor_get(v_toGoalState_2465_, 13);
lean_inc_ref(v_ematch_2466_);
lean_dec_ref(v_toGoalState_2465_);
v_delayedThmInsts_2467_ = lean_ctor_get(v_ematch_2466_, 10);
lean_inc_ref(v_delayedThmInsts_2467_);
lean_dec_ref(v_ematch_2466_);
v___x_2468_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2467_, v_head_2461_);
lean_dec_ref(v_delayedThmInsts_2467_);
if (lean_obj_tag(v___x_2468_) == 1)
{
lean_object* v_val_2469_; lean_object* v___x_2470_; lean_object* v_toGoalState_2471_; lean_object* v_ematch_2472_; lean_object* v_mvarId_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2532_; 
v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_st_ref_take(v___y_2449_);
v_toGoalState_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_ref(v_toGoalState_2471_);
v_ematch_2472_ = lean_ctor_get(v_toGoalState_2471_, 13);
lean_inc_ref(v_ematch_2472_);
v_mvarId_2473_ = lean_ctor_get(v___x_2470_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2533_);
v___x_2475_ = v___x_2470_;
v_isShared_2476_ = v_isSharedCheck_2532_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_mvarId_2473_);
lean_dec(v___x_2470_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2532_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_nextDeclIdx_2477_; lean_object* v_enodeMap_2478_; lean_object* v_exprs_2479_; lean_object* v_parents_2480_; lean_object* v_congrTable_2481_; lean_object* v_appMap_2482_; lean_object* v_indicesFound_2483_; lean_object* v_toProcess_2484_; lean_object* v_internalizing_2485_; uint8_t v_inconsistent_2486_; lean_object* v_nextIdx_2487_; lean_object* v_newRawFacts_2488_; lean_object* v_facts_2489_; lean_object* v_extThms_2490_; lean_object* v_inj_2491_; lean_object* v_split_2492_; lean_object* v_clean_2493_; lean_object* v_sstates_2494_; lean_object* v_goalStack_2495_; uint64_t v_introBase_2496_; lean_object* v_numIntros_2497_; lean_object* v_relevance_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2530_; 
v_nextDeclIdx_2477_ = lean_ctor_get(v_toGoalState_2471_, 0);
v_enodeMap_2478_ = lean_ctor_get(v_toGoalState_2471_, 1);
v_exprs_2479_ = lean_ctor_get(v_toGoalState_2471_, 2);
v_parents_2480_ = lean_ctor_get(v_toGoalState_2471_, 3);
v_congrTable_2481_ = lean_ctor_get(v_toGoalState_2471_, 4);
v_appMap_2482_ = lean_ctor_get(v_toGoalState_2471_, 5);
v_indicesFound_2483_ = lean_ctor_get(v_toGoalState_2471_, 6);
v_toProcess_2484_ = lean_ctor_get(v_toGoalState_2471_, 7);
v_internalizing_2485_ = lean_ctor_get(v_toGoalState_2471_, 8);
v_inconsistent_2486_ = lean_ctor_get_uint8(v_toGoalState_2471_, sizeof(void*)*21 + 8);
v_nextIdx_2487_ = lean_ctor_get(v_toGoalState_2471_, 9);
v_newRawFacts_2488_ = lean_ctor_get(v_toGoalState_2471_, 10);
v_facts_2489_ = lean_ctor_get(v_toGoalState_2471_, 11);
v_extThms_2490_ = lean_ctor_get(v_toGoalState_2471_, 12);
v_inj_2491_ = lean_ctor_get(v_toGoalState_2471_, 14);
v_split_2492_ = lean_ctor_get(v_toGoalState_2471_, 15);
v_clean_2493_ = lean_ctor_get(v_toGoalState_2471_, 16);
v_sstates_2494_ = lean_ctor_get(v_toGoalState_2471_, 17);
v_goalStack_2495_ = lean_ctor_get(v_toGoalState_2471_, 18);
v_introBase_2496_ = lean_ctor_get_uint64(v_toGoalState_2471_, sizeof(void*)*21);
v_numIntros_2497_ = lean_ctor_get(v_toGoalState_2471_, 19);
v_relevance_2498_ = lean_ctor_get(v_toGoalState_2471_, 20);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_toGoalState_2471_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_toGoalState_2471_, 13);
lean_dec(v_unused_2531_);
v___x_2500_ = v_toGoalState_2471_;
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_relevance_2498_);
lean_inc(v_numIntros_2497_);
lean_inc(v_goalStack_2495_);
lean_inc(v_sstates_2494_);
lean_inc(v_clean_2493_);
lean_inc(v_split_2492_);
lean_inc(v_inj_2491_);
lean_inc(v_extThms_2490_);
lean_inc(v_facts_2489_);
lean_inc(v_newRawFacts_2488_);
lean_inc(v_nextIdx_2487_);
lean_inc(v_internalizing_2485_);
lean_inc(v_toProcess_2484_);
lean_inc(v_indicesFound_2483_);
lean_inc(v_appMap_2482_);
lean_inc(v_congrTable_2481_);
lean_inc(v_parents_2480_);
lean_inc(v_exprs_2479_);
lean_inc(v_enodeMap_2478_);
lean_inc(v_nextDeclIdx_2477_);
lean_dec(v_toGoalState_2471_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_thmMap_2502_; lean_object* v_gmt_2503_; lean_object* v_thms_2504_; lean_object* v_newThms_2505_; lean_object* v_numInstances_2506_; lean_object* v_numDelayedInstances_2507_; lean_object* v_num_2508_; lean_object* v_preInstances_2509_; lean_object* v_nextThmIdx_2510_; lean_object* v_matchEqNames_2511_; lean_object* v_delayedThmInsts_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2529_; 
v_thmMap_2502_ = lean_ctor_get(v_ematch_2472_, 0);
v_gmt_2503_ = lean_ctor_get(v_ematch_2472_, 1);
v_thms_2504_ = lean_ctor_get(v_ematch_2472_, 2);
v_newThms_2505_ = lean_ctor_get(v_ematch_2472_, 3);
v_numInstances_2506_ = lean_ctor_get(v_ematch_2472_, 4);
v_numDelayedInstances_2507_ = lean_ctor_get(v_ematch_2472_, 5);
v_num_2508_ = lean_ctor_get(v_ematch_2472_, 6);
v_preInstances_2509_ = lean_ctor_get(v_ematch_2472_, 7);
v_nextThmIdx_2510_ = lean_ctor_get(v_ematch_2472_, 8);
v_matchEqNames_2511_ = lean_ctor_get(v_ematch_2472_, 9);
v_delayedThmInsts_2512_ = lean_ctor_get(v_ematch_2472_, 10);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_ematch_2472_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2514_ = v_ematch_2472_;
v_isShared_2515_ = v_isSharedCheck_2529_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_delayedThmInsts_2512_);
lean_inc(v_matchEqNames_2511_);
lean_inc(v_nextThmIdx_2510_);
lean_inc(v_preInstances_2509_);
lean_inc(v_num_2508_);
lean_inc(v_numDelayedInstances_2507_);
lean_inc(v_numInstances_2506_);
lean_inc(v_newThms_2505_);
lean_inc(v_thms_2504_);
lean_inc(v_gmt_2503_);
lean_inc(v_thmMap_2502_);
lean_dec(v_ematch_2472_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2529_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2512_, v_head_2461_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 10, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_thmMap_2502_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_gmt_2503_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_thms_2504_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_newThms_2505_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_numInstances_2506_);
lean_ctor_set(v_reuseFailAlloc_2528_, 5, v_numDelayedInstances_2507_);
lean_ctor_set(v_reuseFailAlloc_2528_, 6, v_num_2508_);
lean_ctor_set(v_reuseFailAlloc_2528_, 7, v_preInstances_2509_);
lean_ctor_set(v_reuseFailAlloc_2528_, 8, v_nextThmIdx_2510_);
lean_ctor_set(v_reuseFailAlloc_2528_, 9, v_matchEqNames_2511_);
lean_ctor_set(v_reuseFailAlloc_2528_, 10, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 13, v___x_2518_);
v___x_2520_ = v___x_2500_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_nextDeclIdx_2477_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_enodeMap_2478_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_exprs_2479_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_parents_2480_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_congrTable_2481_);
lean_ctor_set(v_reuseFailAlloc_2527_, 5, v_appMap_2482_);
lean_ctor_set(v_reuseFailAlloc_2527_, 6, v_indicesFound_2483_);
lean_ctor_set(v_reuseFailAlloc_2527_, 7, v_toProcess_2484_);
lean_ctor_set(v_reuseFailAlloc_2527_, 8, v_internalizing_2485_);
lean_ctor_set(v_reuseFailAlloc_2527_, 9, v_nextIdx_2487_);
lean_ctor_set(v_reuseFailAlloc_2527_, 10, v_newRawFacts_2488_);
lean_ctor_set(v_reuseFailAlloc_2527_, 11, v_facts_2489_);
lean_ctor_set(v_reuseFailAlloc_2527_, 12, v_extThms_2490_);
lean_ctor_set(v_reuseFailAlloc_2527_, 13, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2527_, 14, v_inj_2491_);
lean_ctor_set(v_reuseFailAlloc_2527_, 15, v_split_2492_);
lean_ctor_set(v_reuseFailAlloc_2527_, 16, v_clean_2493_);
lean_ctor_set(v_reuseFailAlloc_2527_, 17, v_sstates_2494_);
lean_ctor_set(v_reuseFailAlloc_2527_, 18, v_goalStack_2495_);
lean_ctor_set(v_reuseFailAlloc_2527_, 19, v_numIntros_2497_);
lean_ctor_set(v_reuseFailAlloc_2527_, 20, v_relevance_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2527_, sizeof(void*)*21 + 8, v_inconsistent_2486_);
lean_ctor_set_uint64(v_reuseFailAlloc_2527_, sizeof(void*)*21, v_introBase_2496_);
v___x_2520_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2520_);
v___x_2522_ = v___x_2475_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_mvarId_2473_);
v___x_2522_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_st_ref_put(v___y_2449_, v___x_2522_);
v___x_2524_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2469_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref_known(v___x_2524_, 1);
v_as_x27_2447_ = v_tail_2462_;
v_b_2448_ = v___x_2463_;
goto _start;
}
else
{
return v___x_2524_;
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
lean_dec(v___x_2468_);
v_as_x27_2447_ = v_tail_2462_;
v_b_2448_ = v___x_2463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2535_, v_b_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v_as_x27_2535_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2550_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2590_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2590_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2590_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_unbox(v_a_2562_);
lean_dec(v_a_2562_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v_toGoalState_2568_; lean_object* v_ematch_2569_; lean_object* v_delayedThmInsts_2570_; uint8_t v___x_2571_; 
v___x_2567_ = lean_st_ref_get(v_a_2550_);
v_toGoalState_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_toGoalState_2568_);
lean_dec(v___x_2567_);
v_ematch_2569_ = lean_ctor_get(v_toGoalState_2568_, 13);
lean_inc_ref(v_ematch_2569_);
lean_dec_ref(v_toGoalState_2568_);
v_delayedThmInsts_2570_ = lean_ctor_get(v_ematch_2569_, 10);
lean_inc_ref(v_delayedThmInsts_2570_);
lean_dec_ref(v_ematch_2569_);
v___x_2571_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2570_);
lean_dec_ref(v_delayedThmInsts_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_del_object(v___x_2564_);
v___x_2572_ = lean_box(0);
v___x_2573_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2549_, v___x_2572_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2573_, 0);
lean_dec(v_unused_2581_);
v___x_2575_ = v___x_2573_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_dec(v___x_2573_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2572_);
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2572_);
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
return v___x_2573_;
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = lean_box(0);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2582_);
v___x_2584_ = v___x_2564_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_box(0);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2586_);
v___x_2588_ = v___x_2564_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
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
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_a_2591_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2561_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2561_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec(v_toPropagateDown_2599_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2613_, v_x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2616_, v_x_2617_, v_x_2618_);
lean_dec_ref(v_x_2618_);
lean_dec_ref(v_x_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2621_, v_x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2624_, v_x_2625_, v_x_2626_);
lean_dec_ref(v_x_2626_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2628_, lean_object* v_as_x27_2629_, lean_object* v_b_2630_, lean_object* v_a_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2629_, v_b_2630_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2644_, lean_object* v_as_x27_2645_, lean_object* v_b_2646_, lean_object* v_a_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2644_, v_as_x27_2645_, v_b_2646_, v_a_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec(v_as_x27_2645_);
lean_dec(v_as_2644_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2660_, lean_object* v_x_2661_, size_t v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2661_, v_x_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_, lean_object* v_x_2668_){
_start:
{
size_t v_x_20299__boxed_2669_; lean_object* v_res_2670_; 
v_x_20299__boxed_2669_ = lean_unbox_usize(v_x_2667_);
lean_dec(v_x_2667_);
v_res_2670_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2665_, v_x_2666_, v_x_20299__boxed_2669_, v_x_2668_);
lean_dec_ref(v_x_2668_);
lean_dec_ref(v_x_2666_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2671_, lean_object* v_x_2672_, size_t v_x_2673_, lean_object* v_x_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2672_, v_x_2673_, v_x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_){
_start:
{
size_t v_x_20310__boxed_2680_; lean_object* v_res_2681_; 
v_x_20310__boxed_2680_ = lean_unbox_usize(v_x_2678_);
lean_dec(v_x_2678_);
v_res_2681_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2676_, v_x_2677_, v_x_20310__boxed_2680_, v_x_2679_);
lean_dec_ref(v_x_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2682_, lean_object* v_keys_2683_, lean_object* v_vals_2684_, lean_object* v_heq_2685_, lean_object* v_i_2686_, lean_object* v_k_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2683_, v_vals_2684_, v_i_2686_, v_k_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2689_, lean_object* v_keys_2690_, lean_object* v_vals_2691_, lean_object* v_heq_2692_, lean_object* v_i_2693_, lean_object* v_k_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2689_, v_keys_2690_, v_vals_2691_, v_heq_2692_, v_i_2693_, v_k_2694_);
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_vals_2691_);
lean_dec_ref(v_keys_2690_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2696_, lean_object* v_keys_2697_, lean_object* v_vals_2698_, lean_object* v_i_2699_, lean_object* v_k_2700_){
_start:
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = lean_array_get_size(v_keys_2697_);
v___x_2702_ = lean_nat_dec_lt(v_i_2699_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref(v_k_2700_);
lean_dec(v_i_2699_);
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_k_x27_2704_; uint8_t v___x_2705_; 
v_k_x27_2704_ = lean_array_fget_borrowed(v_keys_2697_, v_i_2699_);
lean_inc(v_k_x27_2704_);
lean_inc_ref(v_k_2700_);
v___x_2705_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2696_, v_k_2700_, v_k_x27_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_add(v_i_2699_, v___x_2706_);
lean_dec(v_i_2699_);
v_i_2699_ = v___x_2707_;
goto _start;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_k_2700_);
v___x_2709_ = lean_array_fget_borrowed(v_vals_2698_, v_i_2699_);
lean_dec(v_i_2699_);
lean_inc(v___x_2709_);
lean_inc(v_k_x27_2704_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_k_x27_2704_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2712_, lean_object* v_keys_2713_, lean_object* v_vals_2714_, lean_object* v_i_2715_, lean_object* v_k_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2712_, v_keys_2713_, v_vals_2714_, v_i_2715_, v_k_2716_);
lean_dec_ref(v_vals_2714_);
lean_dec_ref(v_keys_2713_);
lean_dec_ref(v___x_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2718_, lean_object* v_x_2719_, size_t v_x_2720_, lean_object* v_x_2721_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 0)
{
lean_object* v_es_2722_; lean_object* v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; lean_object* v_j_2726_; lean_object* v___x_2727_; 
v_es_2722_ = lean_ctor_get(v_x_2719_, 0);
lean_inc_ref(v_es_2722_);
lean_dec_ref_known(v_x_2719_, 1);
v___x_2723_ = lean_box(2);
v___x_2724_ = ((size_t)31ULL);
v___x_2725_ = lean_usize_land(v_x_2720_, v___x_2724_);
v_j_2726_ = lean_usize_to_nat(v___x_2725_);
v___x_2727_ = lean_array_get(v___x_2723_, v_es_2722_, v_j_2726_);
lean_dec(v_j_2726_);
lean_dec_ref(v_es_2722_);
switch(lean_obj_tag(v___x_2727_))
{
case 0:
{
lean_object* v_key_2728_; lean_object* v_val_2729_; uint8_t v___x_2730_; 
v_key_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc_n(v_key_2728_, 2);
v_val_2729_ = lean_ctor_get(v___x_2727_, 1);
lean_inc(v_val_2729_);
lean_dec_ref_known(v___x_2727_, 2);
v___x_2730_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2718_, v_x_2721_, v_key_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_val_2729_);
lean_dec(v_key_2728_);
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_key_2728_);
lean_ctor_set(v___x_2732_, 1, v_val_2729_);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
case 1:
{
lean_object* v_node_2734_; size_t v___x_2735_; size_t v___x_2736_; 
v_node_2734_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_node_2734_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2735_ = ((size_t)5ULL);
v___x_2736_ = lean_usize_shift_right(v_x_2720_, v___x_2735_);
v_x_2719_ = v_node_2734_;
v_x_2720_ = v___x_2736_;
goto _start;
}
default: 
{
lean_object* v___x_2738_; 
lean_dec_ref(v_x_2721_);
v___x_2738_ = lean_box(0);
return v___x_2738_;
}
}
}
else
{
lean_object* v_ks_2739_; lean_object* v_vs_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_ks_2739_ = lean_ctor_get(v_x_2719_, 0);
lean_inc_ref(v_ks_2739_);
v_vs_2740_ = lean_ctor_get(v_x_2719_, 1);
lean_inc_ref(v_vs_2740_);
lean_dec_ref_known(v_x_2719_, 2);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2718_, v_ks_2739_, v_vs_2740_, v___x_2741_, v_x_2721_);
lean_dec_ref(v_vs_2740_);
lean_dec_ref(v_ks_2739_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
size_t v_x_26627__boxed_2747_; lean_object* v_res_2748_; 
v_x_26627__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v_x_26627__boxed_2747_, v_x_2746_);
lean_dec_ref(v___x_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
uint64_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2749_, v_x_2751_);
v___x_2753_ = lean_uint64_to_usize(v___x_2752_);
lean_inc_ref(v_x_2750_);
v___x_2754_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2749_, v_x_2750_, v___x_2753_, v_x_2751_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2755_, v_x_2756_, v_x_2757_);
lean_dec_ref(v_x_2756_);
lean_dec_ref(v___x_2755_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
lean_object* v_ks_2764_; lean_object* v_vs_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2789_; 
v_ks_2764_ = lean_ctor_get(v_x_2760_, 0);
v_vs_2765_ = lean_ctor_get(v_x_2760_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_x_2760_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2767_ = v_x_2760_;
v_isShared_2768_ = v_isSharedCheck_2789_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_vs_2765_);
lean_inc(v_ks_2764_);
lean_dec(v_x_2760_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2789_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = lean_array_get_size(v_ks_2764_);
v___x_2770_ = lean_nat_dec_lt(v_x_2761_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_x_2761_);
v___x_2771_ = lean_array_push(v_ks_2764_, v_x_2762_);
v___x_2772_ = lean_array_push(v_vs_2765_, v_x_2763_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v___x_2772_);
lean_ctor_set(v___x_2767_, 0, v___x_2771_);
v___x_2774_ = v___x_2767_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v_k_x27_2776_; uint8_t v___x_2777_; 
v_k_x27_2776_ = lean_array_fget_borrowed(v_ks_2764_, v_x_2761_);
lean_inc(v_k_x27_2776_);
lean_inc_ref(v_x_2762_);
v___x_2777_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2759_, v_x_2762_, v_k_x27_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2779_; 
if (v_isShared_2768_ == 0)
{
v___x_2779_ = v___x_2767_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_ks_2764_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_vs_2765_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v_x_2761_, v___x_2780_);
lean_dec(v_x_2761_);
v_x_2760_ = v___x_2779_;
v_x_2761_ = v___x_2781_;
goto _start;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2784_ = lean_array_fset(v_ks_2764_, v_x_2761_, v_x_2762_);
v___x_2785_ = lean_array_fset(v_vs_2765_, v_x_2761_, v_x_2763_);
lean_dec(v_x_2761_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v___x_2785_);
lean_ctor_set(v___x_2767_, 0, v___x_2784_);
v___x_2787_ = v___x_2767_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2790_, lean_object* v_x_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2790_, v_x_2791_, v_x_2792_, v_x_2793_, v_x_2794_);
lean_dec_ref(v___x_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2796_, lean_object* v_n_2797_, lean_object* v_k_2798_, lean_object* v_v_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2796_, v_n_2797_, v___x_2800_, v_k_2798_, v_v_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2802_, lean_object* v_n_2803_, lean_object* v_k_2804_, lean_object* v_v_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2802_, v_n_2803_, v_k_2804_, v_v_2805_);
lean_dec_ref(v___x_2802_);
return v_res_2806_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2808_, lean_object* v_x_2809_, size_t v_x_2810_, size_t v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v_es_2814_; size_t v___x_2815_; size_t v___x_2816_; lean_object* v_j_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_es_2814_ = lean_ctor_get(v_x_2809_, 0);
v___x_2815_ = ((size_t)31ULL);
v___x_2816_ = lean_usize_land(v_x_2810_, v___x_2815_);
v_j_2817_ = lean_usize_to_nat(v___x_2816_);
v___x_2818_ = lean_array_get_size(v_es_2814_);
v___x_2819_ = lean_nat_dec_lt(v_j_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_dec(v_j_2817_);
lean_dec(v_x_2813_);
lean_dec_ref(v_x_2812_);
return v_x_2809_;
}
else
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2858_; 
lean_inc_ref(v_es_2814_);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v_x_2809_, 0);
lean_dec(v_unused_2859_);
v___x_2821_ = v_x_2809_;
v_isShared_2822_ = v_isSharedCheck_2858_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v_x_2809_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2858_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_v_2823_; lean_object* v___x_2824_; lean_object* v_xs_x27_2825_; lean_object* v___y_2827_; 
v_v_2823_ = lean_array_fget(v_es_2814_, v_j_2817_);
v___x_2824_ = lean_box(0);
v_xs_x27_2825_ = lean_array_fset(v_es_2814_, v_j_2817_, v___x_2824_);
switch(lean_obj_tag(v_v_2823_))
{
case 0:
{
lean_object* v_key_2832_; lean_object* v_val_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2843_; 
v_key_2832_ = lean_ctor_get(v_v_2823_, 0);
v_val_2833_ = lean_ctor_get(v_v_2823_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_v_2823_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2835_ = v_v_2823_;
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_val_2833_);
lean_inc(v_key_2832_);
lean_dec(v_v_2823_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
uint8_t v___x_2837_; 
lean_inc(v_key_2832_);
lean_inc_ref(v_x_2812_);
v___x_2837_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2808_, v_x_2812_, v_key_2832_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2835_);
v___x_2838_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2832_, v_val_2833_, v_x_2812_, v_x_2813_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
v___y_2827_ = v___x_2839_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2841_; 
lean_dec(v_val_2833_);
lean_dec(v_key_2832_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v_x_2813_);
lean_ctor_set(v___x_2835_, 0, v_x_2812_);
v___x_2841_ = v___x_2835_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_x_2812_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_x_2813_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2827_ = v___x_2841_;
goto v___jp_2826_;
}
}
}
}
case 1:
{
lean_object* v_node_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2856_; 
v_node_2844_ = lean_ctor_get(v_v_2823_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_v_2823_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2846_ = v_v_2823_;
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_node_2844_);
lean_dec(v_v_2823_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
size_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2848_ = ((size_t)5ULL);
v___x_2849_ = lean_usize_shift_right(v_x_2810_, v___x_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_x_2811_, v___x_2850_);
v___x_2852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2808_, v_node_2844_, v___x_2849_, v___x_2851_, v_x_2812_, v_x_2813_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2852_);
v___x_2854_ = v___x_2846_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v___y_2827_ = v___x_2854_;
goto v___jp_2826_;
}
}
}
default: 
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_x_2812_);
lean_ctor_set(v___x_2857_, 1, v_x_2813_);
v___y_2827_ = v___x_2857_;
goto v___jp_2826_;
}
}
v___jp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = lean_array_fset(v_xs_x27_2825_, v_j_2817_, v___y_2827_);
lean_dec(v_j_2817_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2828_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_ks_2860_; lean_object* v_vs_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2879_; 
v_ks_2860_ = lean_ctor_get(v_x_2809_, 0);
v_vs_2861_ = lean_ctor_get(v_x_2809_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2863_ = v_x_2809_;
v_isShared_2864_ = v_isSharedCheck_2879_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_vs_2861_);
lean_inc(v_ks_2860_);
lean_dec(v_x_2809_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2879_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_ks_2860_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_vs_2861_);
v___x_2866_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v_newNode_2867_; size_t v___x_2868_; uint8_t v___x_2869_; 
v_newNode_2867_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2808_, v___x_2866_, v_x_2812_, v_x_2813_);
v___x_2868_ = ((size_t)7ULL);
v___x_2869_ = lean_usize_dec_le(v___x_2868_, v_x_2811_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2867_);
v___x_2871_ = lean_unsigned_to_nat(4u);
v___x_2872_ = lean_nat_dec_lt(v___x_2870_, v___x_2871_);
lean_dec(v___x_2870_);
if (v___x_2872_ == 0)
{
lean_object* v_ks_2873_; lean_object* v_vs_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_ks_2873_ = lean_ctor_get(v_newNode_2867_, 0);
lean_inc_ref(v_ks_2873_);
v_vs_2874_ = lean_ctor_get(v_newNode_2867_, 1);
lean_inc_ref(v_vs_2874_);
lean_dec_ref(v_newNode_2867_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2808_, v_x_2811_, v_ks_2873_, v_vs_2874_, v___x_2875_, v___x_2876_);
lean_dec_ref(v_vs_2874_);
lean_dec_ref(v_ks_2873_);
return v___x_2877_;
}
else
{
return v_newNode_2867_;
}
}
else
{
return v_newNode_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2880_, size_t v_depth_2881_, lean_object* v_keys_2882_, lean_object* v_vals_2883_, lean_object* v_i_2884_, lean_object* v_entries_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_array_get_size(v_keys_2882_);
v___x_2887_ = lean_nat_dec_lt(v_i_2884_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec(v_i_2884_);
return v_entries_2885_;
}
else
{
lean_object* v_k_2888_; lean_object* v_v_2889_; uint64_t v___x_2890_; size_t v_h_2891_; size_t v___x_2892_; lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; size_t v_h_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_k_2888_ = lean_array_fget_borrowed(v_keys_2882_, v_i_2884_);
v_v_2889_ = lean_array_fget_borrowed(v_vals_2883_, v_i_2884_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2880_, v_k_2888_);
v_h_2891_ = lean_uint64_to_usize(v___x_2890_);
v___x_2892_ = ((size_t)5ULL);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_sub(v_depth_2881_, v___x_2894_);
v___x_2896_ = lean_usize_mul(v___x_2892_, v___x_2895_);
v_h_2897_ = lean_usize_shift_right(v_h_2891_, v___x_2896_);
v___x_2898_ = lean_nat_add(v_i_2884_, v___x_2893_);
lean_dec(v_i_2884_);
lean_inc(v_v_2889_);
lean_inc(v_k_2888_);
v___x_2899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2880_, v_entries_2885_, v_h_2897_, v_depth_2881_, v_k_2888_, v_v_2889_);
v_i_2884_ = v___x_2898_;
v_entries_2885_ = v___x_2899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2901_, lean_object* v_depth_2902_, lean_object* v_keys_2903_, lean_object* v_vals_2904_, lean_object* v_i_2905_, lean_object* v_entries_2906_){
_start:
{
size_t v_depth_boxed_2907_; lean_object* v_res_2908_; 
v_depth_boxed_2907_ = lean_unbox_usize(v_depth_2902_);
lean_dec(v_depth_2902_);
v_res_2908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2901_, v_depth_boxed_2907_, v_keys_2903_, v_vals_2904_, v_i_2905_, v_entries_2906_);
lean_dec_ref(v_vals_2904_);
lean_dec_ref(v_keys_2903_);
lean_dec_ref(v___x_2901_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
size_t v_x_26781__boxed_2915_; size_t v_x_26782__boxed_2916_; lean_object* v_res_2917_; 
v_x_26781__boxed_2915_ = lean_unbox_usize(v_x_2911_);
lean_dec(v_x_2911_);
v_x_26782__boxed_2916_ = lean_unbox_usize(v_x_2912_);
lean_dec(v_x_2912_);
v_res_2917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2909_, v_x_2910_, v_x_26781__boxed_2915_, v_x_26782__boxed_2916_, v_x_2913_, v_x_2914_);
lean_dec_ref(v___x_2909_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_){
_start:
{
uint64_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2918_, v_x_2920_);
v___x_2923_ = lean_uint64_to_usize(v___x_2922_);
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2918_, v_x_2919_, v___x_2923_, v___x_2924_, v_x_2920_, v_x_2921_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2926_, v_x_2927_, v_x_2928_, v_x_2929_);
lean_dec_ref(v___x_2926_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2935_, lean_object* v_rootNew_2936_, uint8_t v_a_2937_, lean_object* v_a_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3135_; 
v_snd_2946_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_3136_);
v___x_2948_ = v_a_2938_;
v_isShared_2949_ = v_isSharedCheck_3135_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_dec(v_a_2938_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3135_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_st_ref_get(v___y_2939_);
lean_inc(v_snd_2946_);
v___x_2952_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2951_, v_snd_2946_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3126_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3126_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3126_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_self_2957_; lean_object* v_next_2958_; lean_object* v_congr_2959_; lean_object* v_target_x3f_2960_; lean_object* v_proof_x3f_2961_; uint8_t v_flipped_2962_; lean_object* v_size_2963_; uint8_t v_interpreted_2964_; uint8_t v_ctor_2965_; uint8_t v_hasLambdas_2966_; uint8_t v_heqProofs_2967_; lean_object* v_idx_2968_; lean_object* v_generation_2969_; lean_object* v_mt_2970_; lean_object* v_sTerms_2971_; uint8_t v_funCC_2972_; lean_object* v_ematchDiagSource_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3124_; 
v_self_2957_ = lean_ctor_get(v_a_2953_, 0);
v_next_2958_ = lean_ctor_get(v_a_2953_, 1);
v_congr_2959_ = lean_ctor_get(v_a_2953_, 3);
v_target_x3f_2960_ = lean_ctor_get(v_a_2953_, 4);
v_proof_x3f_2961_ = lean_ctor_get(v_a_2953_, 5);
v_flipped_2962_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12);
v_size_2963_ = lean_ctor_get(v_a_2953_, 6);
v_interpreted_2964_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12 + 1);
v_ctor_2965_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12 + 2);
v_hasLambdas_2966_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12 + 3);
v_heqProofs_2967_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12 + 4);
v_idx_2968_ = lean_ctor_get(v_a_2953_, 7);
v_generation_2969_ = lean_ctor_get(v_a_2953_, 8);
v_mt_2970_ = lean_ctor_get(v_a_2953_, 9);
v_sTerms_2971_ = lean_ctor_get(v_a_2953_, 10);
v_funCC_2972_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2973_ = lean_ctor_get(v_a_2953_, 11);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_2953_, 2);
lean_dec(v_unused_3125_);
v___x_2975_ = v_a_2953_;
v_isShared_2976_ = v_isSharedCheck_3124_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_ematchDiagSource_2973_);
lean_inc(v_sTerms_2971_);
lean_inc(v_mt_2970_);
lean_inc(v_generation_2969_);
lean_inc(v_idx_2968_);
lean_inc(v_size_2963_);
lean_inc(v_proof_x3f_2961_);
lean_inc(v_target_x3f_2960_);
lean_inc(v_congr_2959_);
lean_inc(v_next_2958_);
lean_inc(v_self_2957_);
lean_dec(v_a_2953_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3124_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2993_; 
lean_inc(v_ematchDiagSource_2973_);
lean_inc(v_sTerms_2971_);
lean_inc(v_mt_2970_);
lean_inc(v_generation_2969_);
lean_inc(v_idx_2968_);
lean_inc(v_size_2963_);
lean_inc(v_proof_x3f_2961_);
lean_inc(v_target_x3f_2960_);
lean_inc_ref(v_rootNew_2936_);
lean_inc_ref(v_next_2958_);
lean_inc_ref(v_self_2957_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 2, v_rootNew_2936_);
v___x_2993_ = v___x_2975_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_self_2957_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_next_2958_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_rootNew_2936_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_congr_2959_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_target_x3f_2960_);
lean_ctor_set(v_reuseFailAlloc_3123_, 5, v_proof_x3f_2961_);
lean_ctor_set(v_reuseFailAlloc_3123_, 6, v_size_2963_);
lean_ctor_set(v_reuseFailAlloc_3123_, 7, v_idx_2968_);
lean_ctor_set(v_reuseFailAlloc_3123_, 8, v_generation_2969_);
lean_ctor_set(v_reuseFailAlloc_3123_, 9, v_mt_2970_);
lean_ctor_set(v_reuseFailAlloc_3123_, 10, v_sTerms_2971_);
lean_ctor_set(v_reuseFailAlloc_3123_, 11, v_ematchDiagSource_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12, v_flipped_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12 + 1, v_interpreted_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12 + 2, v_ctor_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12 + 3, v_hasLambdas_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12 + 4, v_heqProofs_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3123_, sizeof(void*)*12 + 5, v_funCC_2972_);
v___x_2993_ = v_reuseFailAlloc_3123_;
goto v_reusejp_2992_;
}
v___jp_2977_:
{
size_t v___x_2978_; size_t v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_ptr_addr(v_next_2958_);
v___x_2979_ = lean_ptr_addr(v_lhs_2935_);
v___x_2980_ = lean_usize_dec_eq(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2982_; 
lean_del_object(v___x_2955_);
lean_dec(v_snd_2946_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v_next_2958_);
lean_ctor_set(v___x_2948_, 0, v___x_2950_);
v___x_2982_ = v___x_2948_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_next_2958_);
v___x_2982_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_a_2938_ = v___x_2982_;
goto _start;
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_rootNew_2936_);
v___x_2985_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2985_);
v___x_2987_ = v___x_2948_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_snd_2946_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2987_);
v___x_2989_ = v___x_2955_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; 
lean_inc_ref(v___x_2993_);
lean_inc_ref(v_self_2957_);
v___x_2994_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2957_, v___x_2993_, v___y_2939_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_dec_ref_known(v___x_2994_, 1);
if (v_a_2937_ == 0)
{
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
goto v___jp_2977_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2996_ = lean_unsigned_to_nat(3u);
v___x_2997_ = l_Lean_Expr_isAppOfArity(v_self_2957_, v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
goto v___jp_2977_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2993_);
lean_dec_ref(v___x_2993_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v_toGoalState_3000_; lean_object* v_enodeMap_3001_; lean_object* v_congrTable_3002_; lean_object* v___x_3003_; 
v___x_2999_ = lean_st_ref_get(v___y_2939_);
v_toGoalState_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_toGoalState_3000_);
lean_dec(v___x_2999_);
v_enodeMap_3001_ = lean_ctor_get(v_toGoalState_3000_, 1);
lean_inc_ref(v_enodeMap_3001_);
v_congrTable_3002_ = lean_ctor_get(v_toGoalState_3000_, 4);
lean_inc_ref(v_congrTable_3002_);
lean_dec_ref(v_toGoalState_3000_);
lean_inc_ref(v_self_2957_);
v___x_3003_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3001_, v_congrTable_3002_, v_self_2957_);
lean_dec_ref(v_congrTable_3002_);
lean_dec_ref(v_enodeMap_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
goto v___jp_2977_;
}
else
{
lean_object* v_val_3004_; lean_object* v_fst_3005_; lean_object* v___x_3006_; 
v_val_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_fst_3005_ = lean_ctor_get(v_val_3004_, 0);
lean_inc(v_fst_3005_);
lean_dec(v_val_3004_);
v___x_3006_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3005_, v___y_2940_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; uint8_t v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = lean_unbox(v_a_3007_);
lean_dec(v_a_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v_toGoalState_3010_; lean_object* v_mvarId_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3106_; 
v___x_3009_ = lean_st_ref_take(v___y_2939_);
v_toGoalState_3010_ = lean_ctor_get(v___x_3009_, 0);
v_mvarId_3011_ = lean_ctor_get(v___x_3009_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3106_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_mvarId_3011_);
lean_inc(v_toGoalState_3010_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3106_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_nextDeclIdx_3015_; lean_object* v_enodeMap_3016_; lean_object* v_exprs_3017_; lean_object* v_parents_3018_; lean_object* v_congrTable_3019_; lean_object* v_appMap_3020_; lean_object* v_indicesFound_3021_; lean_object* v_toProcess_3022_; lean_object* v_internalizing_3023_; uint8_t v_inconsistent_3024_; lean_object* v_nextIdx_3025_; lean_object* v_newRawFacts_3026_; lean_object* v_facts_3027_; lean_object* v_extThms_3028_; lean_object* v_ematch_3029_; lean_object* v_inj_3030_; lean_object* v_split_3031_; lean_object* v_clean_3032_; lean_object* v_sstates_3033_; lean_object* v_goalStack_3034_; uint64_t v_introBase_3035_; lean_object* v_numIntros_3036_; lean_object* v_relevance_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3105_; 
v_nextDeclIdx_3015_ = lean_ctor_get(v_toGoalState_3010_, 0);
v_enodeMap_3016_ = lean_ctor_get(v_toGoalState_3010_, 1);
v_exprs_3017_ = lean_ctor_get(v_toGoalState_3010_, 2);
v_parents_3018_ = lean_ctor_get(v_toGoalState_3010_, 3);
v_congrTable_3019_ = lean_ctor_get(v_toGoalState_3010_, 4);
v_appMap_3020_ = lean_ctor_get(v_toGoalState_3010_, 5);
v_indicesFound_3021_ = lean_ctor_get(v_toGoalState_3010_, 6);
v_toProcess_3022_ = lean_ctor_get(v_toGoalState_3010_, 7);
v_internalizing_3023_ = lean_ctor_get(v_toGoalState_3010_, 8);
v_inconsistent_3024_ = lean_ctor_get_uint8(v_toGoalState_3010_, sizeof(void*)*21 + 8);
v_nextIdx_3025_ = lean_ctor_get(v_toGoalState_3010_, 9);
v_newRawFacts_3026_ = lean_ctor_get(v_toGoalState_3010_, 10);
v_facts_3027_ = lean_ctor_get(v_toGoalState_3010_, 11);
v_extThms_3028_ = lean_ctor_get(v_toGoalState_3010_, 12);
v_ematch_3029_ = lean_ctor_get(v_toGoalState_3010_, 13);
v_inj_3030_ = lean_ctor_get(v_toGoalState_3010_, 14);
v_split_3031_ = lean_ctor_get(v_toGoalState_3010_, 15);
v_clean_3032_ = lean_ctor_get(v_toGoalState_3010_, 16);
v_sstates_3033_ = lean_ctor_get(v_toGoalState_3010_, 17);
v_goalStack_3034_ = lean_ctor_get(v_toGoalState_3010_, 18);
v_introBase_3035_ = lean_ctor_get_uint64(v_toGoalState_3010_, sizeof(void*)*21);
v_numIntros_3036_ = lean_ctor_get(v_toGoalState_3010_, 19);
v_relevance_3037_ = lean_ctor_get(v_toGoalState_3010_, 20);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_toGoalState_3010_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3039_ = v_toGoalState_3010_;
v_isShared_3040_ = v_isSharedCheck_3105_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_relevance_3037_);
lean_inc(v_numIntros_3036_);
lean_inc(v_goalStack_3034_);
lean_inc(v_sstates_3033_);
lean_inc(v_clean_3032_);
lean_inc(v_split_3031_);
lean_inc(v_inj_3030_);
lean_inc(v_ematch_3029_);
lean_inc(v_extThms_3028_);
lean_inc(v_facts_3027_);
lean_inc(v_newRawFacts_3026_);
lean_inc(v_nextIdx_3025_);
lean_inc(v_internalizing_3023_);
lean_inc(v_toProcess_3022_);
lean_inc(v_indicesFound_3021_);
lean_inc(v_appMap_3020_);
lean_inc(v_congrTable_3019_);
lean_inc(v_parents_3018_);
lean_inc(v_exprs_3017_);
lean_inc(v_enodeMap_3016_);
lean_inc(v_nextDeclIdx_3015_);
lean_dec(v_toGoalState_3010_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3105_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3041_ = lean_box(0);
lean_inc_ref(v_self_2957_);
v___x_3042_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3016_, v_congrTable_3019_, v_self_2957_, v___x_3041_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 4, v___x_3042_);
v___x_3044_ = v___x_3039_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_nextDeclIdx_3015_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_enodeMap_3016_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_exprs_3017_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_parents_3018_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_appMap_3020_);
lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_indicesFound_3021_);
lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_toProcess_3022_);
lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_internalizing_3023_);
lean_ctor_set(v_reuseFailAlloc_3104_, 9, v_nextIdx_3025_);
lean_ctor_set(v_reuseFailAlloc_3104_, 10, v_newRawFacts_3026_);
lean_ctor_set(v_reuseFailAlloc_3104_, 11, v_facts_3027_);
lean_ctor_set(v_reuseFailAlloc_3104_, 12, v_extThms_3028_);
lean_ctor_set(v_reuseFailAlloc_3104_, 13, v_ematch_3029_);
lean_ctor_set(v_reuseFailAlloc_3104_, 14, v_inj_3030_);
lean_ctor_set(v_reuseFailAlloc_3104_, 15, v_split_3031_);
lean_ctor_set(v_reuseFailAlloc_3104_, 16, v_clean_3032_);
lean_ctor_set(v_reuseFailAlloc_3104_, 17, v_sstates_3033_);
lean_ctor_set(v_reuseFailAlloc_3104_, 18, v_goalStack_3034_);
lean_ctor_set(v_reuseFailAlloc_3104_, 19, v_numIntros_3036_);
lean_ctor_set(v_reuseFailAlloc_3104_, 20, v_relevance_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*21 + 8, v_inconsistent_3024_);
lean_ctor_set_uint64(v_reuseFailAlloc_3104_, sizeof(void*)*21, v_introBase_3035_);
v___x_3044_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3046_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3044_);
v___x_3046_ = v___x_3013_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_mvarId_3011_);
v___x_3046_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_st_ref_put(v___y_2939_, v___x_3046_);
lean_inc_ref(v_rootNew_2936_);
lean_inc_ref(v_next_2958_);
lean_inc_ref_n(v_self_2957_, 3);
v___x_3048_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3048_, 0, v_self_2957_);
lean_ctor_set(v___x_3048_, 1, v_next_2958_);
lean_ctor_set(v___x_3048_, 2, v_rootNew_2936_);
lean_ctor_set(v___x_3048_, 3, v_self_2957_);
lean_ctor_set(v___x_3048_, 4, v_target_x3f_2960_);
lean_ctor_set(v___x_3048_, 5, v_proof_x3f_2961_);
lean_ctor_set(v___x_3048_, 6, v_size_2963_);
lean_ctor_set(v___x_3048_, 7, v_idx_2968_);
lean_ctor_set(v___x_3048_, 8, v_generation_2969_);
lean_ctor_set(v___x_3048_, 9, v_mt_2970_);
lean_ctor_set(v___x_3048_, 10, v_sTerms_2971_);
lean_ctor_set(v___x_3048_, 11, v_ematchDiagSource_2973_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12, v_flipped_2962_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12 + 1, v_interpreted_2964_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12 + 2, v_ctor_2965_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12 + 3, v_hasLambdas_2966_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12 + 4, v_heqProofs_2967_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*12 + 5, v_funCC_2972_);
v___x_3049_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2957_, v___x_3048_, v___y_2939_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref_known(v___x_3049_, 1);
v___x_3050_ = lean_st_ref_get(v___y_2939_);
lean_inc(v_fst_3005_);
v___x_3051_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3050_, v_fst_3005_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___x_3050_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v_self_3053_; lean_object* v_next_3054_; lean_object* v_root_3055_; lean_object* v_target_x3f_3056_; lean_object* v_proof_x3f_3057_; uint8_t v_flipped_3058_; lean_object* v_size_3059_; uint8_t v_interpreted_3060_; uint8_t v_ctor_3061_; uint8_t v_hasLambdas_3062_; uint8_t v_heqProofs_3063_; lean_object* v_idx_3064_; lean_object* v_generation_3065_; lean_object* v_mt_3066_; lean_object* v_sTerms_3067_; uint8_t v_funCC_3068_; lean_object* v_ematchDiagSource_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3085_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v_self_3053_ = lean_ctor_get(v_a_3052_, 0);
v_next_3054_ = lean_ctor_get(v_a_3052_, 1);
v_root_3055_ = lean_ctor_get(v_a_3052_, 2);
v_target_x3f_3056_ = lean_ctor_get(v_a_3052_, 4);
v_proof_x3f_3057_ = lean_ctor_get(v_a_3052_, 5);
v_flipped_3058_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12);
v_size_3059_ = lean_ctor_get(v_a_3052_, 6);
v_interpreted_3060_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12 + 1);
v_ctor_3061_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12 + 2);
v_hasLambdas_3062_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12 + 3);
v_heqProofs_3063_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12 + 4);
v_idx_3064_ = lean_ctor_get(v_a_3052_, 7);
v_generation_3065_ = lean_ctor_get(v_a_3052_, 8);
v_mt_3066_ = lean_ctor_get(v_a_3052_, 9);
v_sTerms_3067_ = lean_ctor_get(v_a_3052_, 10);
v_funCC_3068_ = lean_ctor_get_uint8(v_a_3052_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3069_ = lean_ctor_get(v_a_3052_, 11);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3052_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v_a_3052_, 3);
lean_dec(v_unused_3086_);
v___x_3071_ = v_a_3052_;
v_isShared_3072_ = v_isSharedCheck_3085_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_ematchDiagSource_3069_);
lean_inc(v_sTerms_3067_);
lean_inc(v_mt_3066_);
lean_inc(v_generation_3065_);
lean_inc(v_idx_3064_);
lean_inc(v_size_3059_);
lean_inc(v_proof_x3f_3057_);
lean_inc(v_target_x3f_3056_);
lean_inc(v_root_3055_);
lean_inc(v_next_3054_);
lean_inc(v_self_3053_);
lean_dec(v_a_3052_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3085_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 3, v_self_2957_);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_self_3053_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_next_3054_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_root_3055_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_self_2957_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v_target_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_proof_x3f_3057_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_size_3059_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_idx_3064_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_generation_3065_);
lean_ctor_set(v_reuseFailAlloc_3084_, 9, v_mt_3066_);
lean_ctor_set(v_reuseFailAlloc_3084_, 10, v_sTerms_3067_);
lean_ctor_set(v_reuseFailAlloc_3084_, 11, v_ematchDiagSource_3069_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12, v_flipped_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 1, v_interpreted_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 2, v_ctor_3061_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 3, v_hasLambdas_3062_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 4, v_heqProofs_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*12 + 5, v_funCC_3068_);
v___x_3074_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3005_, v___x_3074_, v___y_2939_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_dec_ref_known(v___x_3075_, 1);
goto v___jp_2977_;
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v_next_2958_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_fst_3005_);
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_self_2957_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3087_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3051_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3051_);
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
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_fst_3005_);
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_self_2957_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3095_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3049_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3049_);
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
}
}
}
else
{
lean_dec(v_fst_3005_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
goto v___jp_2977_;
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_fst_3005_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_self_2957_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3107_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3006_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3006_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
goto v___jp_2977_;
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_self_2957_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3115_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_2994_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_2994_);
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
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3127_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_2952_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_2952_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3137_, lean_object* v_rootNew_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v_a_26965__boxed_3148_; lean_object* v_res_3149_; 
v_a_26965__boxed_3148_ = lean_unbox(v_a_3139_);
v_res_3149_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3137_, v_rootNew_3138_, v_a_26965__boxed_3148_, v_a_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v_lhs_3137_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3150_, lean_object* v_rootNew_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3151_, v_a_3156_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; lean_object* v___x_3168_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = lean_box(0);
lean_inc_ref(v_lhs_3150_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v_lhs_3150_);
v___x_3167_ = lean_unbox(v_a_3164_);
lean_dec(v_a_3164_);
v___x_3168_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3150_, v_rootNew_3151_, v___x_3167_, v___x_3166_, v_a_3152_, v_a_3156_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec_ref(v_lhs_3150_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3182_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3171_ = v___x_3168_;
v_isShared_3172_ = v_isSharedCheck_3182_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3182_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v_fst_3173_; 
v_fst_3173_ = lean_ctor_get(v_a_3169_, 0);
lean_inc(v_fst_3173_);
lean_dec(v_a_3169_);
if (lean_obj_tag(v_fst_3173_) == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_box(0);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3174_);
v___x_3176_ = v___x_3171_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_object* v_val_3178_; lean_object* v___x_3180_; 
v_val_3178_ = lean_ctor_get(v_fst_3173_, 0);
lean_inc(v_val_3178_);
lean_dec_ref_known(v_fst_3173_, 1);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v_val_3178_);
v___x_3180_ = v___x_3171_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_val_3178_);
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
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v_a_3183_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3168_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3168_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_rootNew_3151_);
lean_dec_ref(v_lhs_3150_);
v_a_3191_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3163_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3163_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3199_, lean_object* v_rootNew_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3199_, v_rootNew_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec(v_a_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3213_, v_x_3215_, v_x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3218_, lean_object* v_00_u03b2_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3218_, v_00_u03b2_3219_, v_x_3220_, v_x_3221_);
lean_dec_ref(v_x_3220_);
lean_dec_ref(v___x_3218_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3223_, v_x_3225_, v_x_3226_, v_x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3229_, lean_object* v_00_u03b2_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3229_, v_00_u03b2_3230_, v_x_3231_, v_x_3232_, v_x_3233_);
lean_dec_ref(v___x_3229_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3235_, lean_object* v_rootNew_3236_, uint8_t v_a_3237_, lean_object* v_inst_3238_, lean_object* v_a_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3235_, v_rootNew_3236_, v_a_3237_, v_a_3239_, v___y_3240_, v___y_3244_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3252_, lean_object* v_rootNew_3253_, lean_object* v_a_3254_, lean_object* v_inst_3255_, lean_object* v_a_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_a_27350__boxed_3268_; lean_object* v_res_3269_; 
v_a_27350__boxed_3268_ = lean_unbox(v_a_3254_);
v_res_3269_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3252_, v_rootNew_3253_, v_a_27350__boxed_3268_, v_inst_3255_, v_a_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v_lhs_3252_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_x_3272_, size_t v_x_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v___x_3275_; 
lean_inc_ref(v_x_3272_);
v___x_3275_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3270_, v_x_3272_, v_x_3273_, v_x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3276_, lean_object* v_00_u03b2_3277_, lean_object* v_x_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
size_t v_x_27393__boxed_3281_; lean_object* v_res_3282_; 
v_x_27393__boxed_3281_ = lean_unbox_usize(v_x_3279_);
lean_dec(v_x_3279_);
v_res_3282_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3276_, v_00_u03b2_3277_, v_x_3278_, v_x_27393__boxed_3281_, v_x_3280_);
lean_dec_ref(v_x_3278_);
lean_dec_ref(v___x_3276_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3283_, lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, size_t v_x_3286_, size_t v_x_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3283_, v_x_3285_, v_x_3286_, v_x_3287_, v_x_3288_, v_x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3291_, lean_object* v_00_u03b2_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
size_t v_x_27407__boxed_3298_; size_t v_x_27408__boxed_3299_; lean_object* v_res_3300_; 
v_x_27407__boxed_3298_ = lean_unbox_usize(v_x_3294_);
lean_dec(v_x_3294_);
v_x_27408__boxed_3299_ = lean_unbox_usize(v_x_3295_);
lean_dec(v_x_3295_);
v_res_3300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3291_, v_00_u03b2_3292_, v_x_3293_, v_x_27407__boxed_3298_, v_x_27408__boxed_3299_, v_x_3296_, v_x_3297_);
lean_dec_ref(v___x_3291_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3301_, lean_object* v_00_u03b2_3302_, lean_object* v_keys_3303_, lean_object* v_vals_3304_, lean_object* v_heq_3305_, lean_object* v_i_3306_, lean_object* v_k_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3301_, v_keys_3303_, v_vals_3304_, v_i_3306_, v_k_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3309_, lean_object* v_00_u03b2_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_heq_3313_, lean_object* v_i_3314_, lean_object* v_k_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3309_, v_00_u03b2_3310_, v_keys_3311_, v_vals_3312_, v_heq_3313_, v_i_3314_, v_k_3315_);
lean_dec_ref(v_vals_3312_);
lean_dec_ref(v_keys_3311_);
lean_dec_ref(v___x_3309_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3317_, lean_object* v_00_u03b2_3318_, lean_object* v_n_3319_, lean_object* v_k_3320_, lean_object* v_v_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3317_, v_n_3319_, v_k_3320_, v_v_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3323_, lean_object* v_00_u03b2_3324_, lean_object* v_n_3325_, lean_object* v_k_3326_, lean_object* v_v_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3323_, v_00_u03b2_3324_, v_n_3325_, v_k_3326_, v_v_3327_);
lean_dec_ref(v___x_3323_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3329_, lean_object* v_00_u03b2_3330_, size_t v_depth_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_entries_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3329_, v_depth_3331_, v_keys_3332_, v_vals_3333_, v_i_3335_, v_entries_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3338_, lean_object* v_00_u03b2_3339_, lean_object* v_depth_3340_, lean_object* v_keys_3341_, lean_object* v_vals_3342_, lean_object* v_heq_3343_, lean_object* v_i_3344_, lean_object* v_entries_3345_){
_start:
{
size_t v_depth_boxed_3346_; lean_object* v_res_3347_; 
v_depth_boxed_3346_ = lean_unbox_usize(v_depth_3340_);
lean_dec(v_depth_3340_);
v_res_3347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3338_, v_00_u03b2_3339_, v_depth_boxed_3346_, v_keys_3341_, v_vals_3342_, v_heq_3343_, v_i_3344_, v_entries_3345_);
lean_dec_ref(v_vals_3342_);
lean_dec_ref(v_keys_3341_);
lean_dec_ref(v___x_3338_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3348_, lean_object* v_00_u03b2_3349_, lean_object* v_x_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3348_, v_x_3350_, v_x_3351_, v_x_3352_, v_x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3355_, lean_object* v_00_u03b2_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v_x_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3355_, v_00_u03b2_3356_, v_x_3357_, v_x_3358_, v_x_3359_, v_x_3360_);
lean_dec_ref(v___x_3355_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3362_, lean_object* v_b_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
if (lean_obj_tag(v_as_x27_3362_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_b_3363_);
return v___x_3375_;
}
else
{
lean_object* v_head_3376_; lean_object* v_tail_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_head_3376_ = lean_ctor_get(v_as_x27_3362_, 0);
v_tail_3377_ = lean_ctor_get(v_as_x27_3362_, 1);
v___x_3378_ = lean_box(0);
lean_inc(v_head_3376_);
v___x_3379_ = l_Lean_Meta_Grind_propagateUp(v_head_3376_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_dec_ref_known(v___x_3379_, 1);
v_as_x27_3362_ = v_tail_3377_;
v_b_3363_ = v___x_3378_;
goto _start;
}
else
{
return v___x_3379_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3381_, lean_object* v_b_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3381_, v_b_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec(v_as_x27_3381_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
if (lean_obj_tag(v_as_x27_3395_) == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_b_3396_);
return v___x_3408_;
}
else
{
lean_object* v_head_3409_; lean_object* v_tail_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_head_3409_ = lean_ctor_get(v_as_x27_3395_, 0);
v_tail_3410_ = lean_ctor_get(v_as_x27_3395_, 1);
v___x_3411_ = lean_box(0);
lean_inc(v_head_3409_);
v___x_3412_ = l_Lean_Meta_Grind_propagateDown(v_head_3409_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref_known(v___x_3412_, 1);
v_as_x27_3395_ = v_tail_3410_;
v_b_3396_ = v___x_3411_;
goto _start;
}
else
{
return v___x_3412_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3414_, lean_object* v_b_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3414_, v_b_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec(v_as_x27_3414_);
return v_res_3427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_cls_3431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3432_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3433_ = l_Lean_Name_append(v___x_3432_, v_cls_3431_);
return v___x_3433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
return v___x_3442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3445_ = l_Lean_stringToMessageData(v___x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3446_, uint8_t v_isHEq_3447_, lean_object* v_lhs_3448_, lean_object* v_rhs_3449_, lean_object* v_lhsNode_3450_, lean_object* v_rhsNode_3451_, lean_object* v_lhsRoot_3452_, lean_object* v_rhsRoot_3453_, uint8_t v_flipped_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3519_; uint8_t v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; uint8_t v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; uint8_t v___y_3555_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; uint8_t v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v_toCold_3712_; lean_object* v_options_3713_; lean_object* v_inheritedTraceOptions_3714_; uint8_t v_hasTrace_3715_; lean_object* v_cls_3716_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v_fns_u2082_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v_fns_u2081_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; 
v_toCold_3712_ = lean_ctor_get(v_a_3463_, 0);
v_options_3713_ = lean_ctor_get(v_toCold_3712_, 2);
v_inheritedTraceOptions_3714_ = lean_ctor_get(v_toCold_3712_, 11);
v_hasTrace_3715_ = lean_ctor_get_uint8(v_options_3713_, sizeof(void*)*1);
v_cls_3716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3715_ == 0)
{
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
v___y_3843_ = v_a_3462_;
v___y_3844_ = v_a_3463_;
v___y_3845_ = v_a_3464_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3916_; uint8_t v___x_3917_; 
v___x_3916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3714_, v_options_3713_, v___x_3916_);
if (v___x_3917_ == 0)
{
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
v___y_3843_ = v_a_3462_;
v___y_3844_ = v_a_3463_;
v___y_3845_ = v_a_3464_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_Meta_Grind_updateLastTag(v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; 
lean_dec_ref_known(v___x_3918_, 1);
lean_inc_ref(v_lhs_3448_);
v___x_3919_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3448_, v_a_3455_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
lean_inc_ref(v_rhs_3449_);
v___x_3921_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3449_, v_a_3455_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_a_3920_);
v___x_3925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v_a_3922_);
v___x_3928_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3716_, v___x_3927_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_dec_ref_known(v___x_3928_, 1);
v___y_3836_ = v_a_3455_;
v___y_3837_ = v_a_3456_;
v___y_3838_ = v_a_3457_;
v___y_3839_ = v_a_3458_;
v___y_3840_ = v_a_3459_;
v___y_3841_ = v_a_3460_;
v___y_3842_ = v_a_3461_;
v___y_3843_ = v_a_3462_;
v___y_3844_ = v_a_3463_;
v___y_3845_ = v_a_3464_;
goto v___jp_3835_;
}
else
{
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhsNode_3450_);
lean_dec_ref(v_rhs_3449_);
lean_dec_ref(v_lhs_3448_);
lean_dec_ref(v_proof_3446_);
return v___x_3928_;
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3920_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhsNode_3450_);
lean_dec_ref(v_rhs_3449_);
lean_dec_ref(v_lhs_3448_);
lean_dec_ref(v_proof_3446_);
v_a_3929_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3921_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3921_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhsNode_3450_);
lean_dec_ref(v_rhs_3449_);
lean_dec_ref(v_lhs_3448_);
lean_dec_ref(v_proof_3446_);
v_a_3937_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3919_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3919_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhsNode_3450_);
lean_dec_ref(v_rhs_3449_);
lean_dec_ref(v_lhs_3448_);
lean_dec_ref(v_proof_3446_);
return v___x_3918_;
}
}
}
v___jp_3466_:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3509_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3486_ = v___x_3483_;
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3483_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3509_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
uint8_t v___x_3488_; 
v___x_3488_ = lean_unbox(v_a_3484_);
lean_dec(v_a_3484_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_del_object(v___x_3486_);
v___x_3489_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3471_);
lean_dec(v___y_3471_);
v___x_3490_ = lean_box(0);
v___x_3491_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3489_, v___x_3490_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___x_3489_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3492_; 
lean_dec_ref_known(v___x_3491_, 1);
v___x_3492_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3470_, v___x_3490_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v___x_3493_; 
lean_dec_ref_known(v___x_3492_, 1);
v___x_3493_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3468_, v___y_3467_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v___y_3468_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v___x_3494_; 
lean_dec_ref_known(v___x_3493_, 1);
v___x_3494_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3469_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3503_; 
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; 
v_unused_3504_ = lean_ctor_get(v___x_3494_, 0);
lean_dec(v_unused_3504_);
v___x_3496_ = v___x_3494_;
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
else
{
lean_dec(v___x_3494_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
uint8_t v___x_3498_; 
v___x_3498_ = l_Lean_Expr_isTrue(v___y_3472_);
lean_dec_ref(v___y_3472_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v___y_3470_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3490_);
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3490_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
else
{
lean_object* v___x_3502_; 
lean_del_object(v___x_3496_);
v___x_3502_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3470_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3470_);
return v___x_3502_;
}
}
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3470_);
return v___x_3494_;
}
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
return v___x_3493_;
}
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v___x_3492_;
}
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v___x_3491_;
}
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3467_);
v___x_3505_ = lean_box(0);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3505_);
v___x_3507_ = v___x_3486_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v___y_3467_);
v_a_3510_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3483_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3483_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
v___jp_3518_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_inc_ref(v___y_3519_);
v___x_3556_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3556_, 0, v___y_3519_);
lean_ctor_set(v___x_3556_, 1, v___y_3523_);
lean_ctor_set(v___x_3556_, 2, v___y_3551_);
lean_ctor_set(v___x_3556_, 3, v___y_3532_);
lean_ctor_set(v___x_3556_, 4, v___y_3544_);
lean_ctor_set(v___x_3556_, 5, v___y_3554_);
lean_ctor_set(v___x_3556_, 6, v___y_3531_);
lean_ctor_set(v___x_3556_, 7, v___y_3539_);
lean_ctor_set(v___x_3556_, 8, v___y_3538_);
lean_ctor_set(v___x_3556_, 9, v___y_3528_);
lean_ctor_set(v___x_3556_, 10, v___y_3535_);
lean_ctor_set(v___x_3556_, 11, v___y_3537_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12, v___y_3520_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12 + 1, v___y_3526_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12 + 2, v___y_3525_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12 + 3, v___y_3555_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12 + 4, v___y_3548_);
lean_ctor_set_uint8(v___x_3556_, sizeof(void*)*12 + 5, v___y_3546_);
lean_inc_ref(v___y_3536_);
v___x_3557_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3536_, v___x_3556_, v___y_3529_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref_known(v___x_3557_, 1);
lean_inc_ref(v___y_3550_);
v___x_3558_ = l_Lean_Meta_Grind_propagateBeta(v___y_3550_, v___y_3534_, v___y_3529_, v___y_3542_, v___y_3527_, v___y_3552_, v___y_3541_, v___y_3533_, v___y_3543_, v___y_3524_, v___y_3545_, v___y_3553_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3559_; 
lean_dec_ref_known(v___x_3558_, 1);
lean_inc_ref(v___y_3547_);
v___x_3559_ = l_Lean_Meta_Grind_propagateBeta(v___y_3547_, v___y_3549_, v___y_3529_, v___y_3542_, v___y_3527_, v___y_3552_, v___y_3541_, v___y_3533_, v___y_3543_, v___y_3524_, v___y_3545_, v___y_3553_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v___x_3560_; 
lean_dec_ref_known(v___x_3559_, 1);
v___x_3560_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v___y_3530_, v_lhsRoot_3452_, v___y_3548_, v___y_3529_, v___y_3543_, v___y_3524_, v___y_3545_, v___y_3553_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3540_, v___y_3529_);
lean_dec_ref(v___y_3540_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3563_; 
lean_dec_ref_known(v___x_3562_, 1);
lean_inc_ref(v___y_3536_);
v___x_3563_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3521_, v___y_3536_, v___y_3529_, v___y_3542_, v___y_3527_, v___y_3552_, v___y_3541_, v___y_3533_, v___y_3543_, v___y_3524_, v___y_3545_, v___y_3553_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref_known(v___x_3563_, 1);
v___x_3564_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3529_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; uint8_t v___x_3566_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3566_ = lean_unbox(v_a_3565_);
lean_dec(v_a_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
v___x_3567_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3519_, v___y_3529_, v___y_3542_, v___y_3527_, v___y_3552_, v___y_3541_, v___y_3533_, v___y_3543_, v___y_3524_, v___y_3545_, v___y_3553_);
lean_dec_ref(v___y_3519_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_dec_ref_known(v___x_3567_, 1);
v___y_3467_ = v___y_3547_;
v___y_3468_ = v___y_3550_;
v___y_3469_ = v_a_3561_;
v___y_3470_ = v___y_3522_;
v___y_3471_ = v___y_3521_;
v___y_3472_ = v___y_3536_;
v___y_3473_ = v___y_3529_;
v___y_3474_ = v___y_3542_;
v___y_3475_ = v___y_3527_;
v___y_3476_ = v___y_3552_;
v___y_3477_ = v___y_3541_;
v___y_3478_ = v___y_3533_;
v___y_3479_ = v___y_3543_;
v___y_3480_ = v___y_3524_;
v___y_3481_ = v___y_3545_;
v___y_3482_ = v___y_3553_;
goto v___jp_3466_;
}
else
{
lean_dec(v_a_3561_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
return v___x_3567_;
}
}
else
{
lean_dec_ref(v___y_3519_);
v___y_3467_ = v___y_3547_;
v___y_3468_ = v___y_3550_;
v___y_3469_ = v_a_3561_;
v___y_3470_ = v___y_3522_;
v___y_3471_ = v___y_3521_;
v___y_3472_ = v___y_3536_;
v___y_3473_ = v___y_3529_;
v___y_3474_ = v___y_3542_;
v___y_3475_ = v___y_3527_;
v___y_3476_ = v___y_3552_;
v___y_3477_ = v___y_3541_;
v___y_3478_ = v___y_3533_;
v___y_3479_ = v___y_3543_;
v___y_3480_ = v___y_3524_;
v___y_3481_ = v___y_3545_;
v___y_3482_ = v___y_3553_;
goto v___jp_3466_;
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec(v_a_3561_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
v_a_3568_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3564_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3564_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_dec(v_a_3561_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
return v___x_3563_;
}
}
else
{
lean_dec(v_a_3561_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
return v___x_3562_;
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
v_a_3576_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3560_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3560_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_lhsRoot_3452_);
return v___x_3559_;
}
}
else
{
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_lhsRoot_3452_);
return v___x_3558_;
}
}
else
{
lean_dec_ref(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_lhsRoot_3452_);
return v___x_3557_;
}
}
v___jp_3584_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_st_ref_get(v___y_3599_);
v___x_3609_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3608_, v___y_3600_, v___y_3590_, v___y_3595_, v___y_3591_, v___y_3606_);
lean_dec(v___x_3608_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v_self_3611_; lean_object* v_root_3612_; lean_object* v_congr_3613_; lean_object* v_target_x3f_3614_; lean_object* v_proof_x3f_3615_; uint8_t v_flipped_3616_; lean_object* v_size_3617_; uint8_t v_interpreted_3618_; uint8_t v_ctor_3619_; uint8_t v_hasLambdas_3620_; lean_object* v_idx_3621_; lean_object* v_generation_3622_; lean_object* v_mt_3623_; lean_object* v_sTerms_3624_; uint8_t v_funCC_3625_; lean_object* v_ematchDiagSource_3626_; lean_object* v___x_3627_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v_self_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc_ref(v_self_3611_);
v_root_3612_ = lean_ctor_get(v_a_3610_, 2);
lean_inc_ref(v_root_3612_);
v_congr_3613_ = lean_ctor_get(v_a_3610_, 3);
lean_inc_ref(v_congr_3613_);
v_target_x3f_3614_ = lean_ctor_get(v_a_3610_, 4);
lean_inc(v_target_x3f_3614_);
v_proof_x3f_3615_ = lean_ctor_get(v_a_3610_, 5);
lean_inc(v_proof_x3f_3615_);
v_flipped_3616_ = lean_ctor_get_uint8(v_a_3610_, sizeof(void*)*12);
v_size_3617_ = lean_ctor_get(v_a_3610_, 6);
v_interpreted_3618_ = lean_ctor_get_uint8(v_a_3610_, sizeof(void*)*12 + 1);
v_ctor_3619_ = lean_ctor_get_uint8(v_a_3610_, sizeof(void*)*12 + 2);
v_hasLambdas_3620_ = lean_ctor_get_uint8(v_a_3610_, sizeof(void*)*12 + 3);
v_idx_3621_ = lean_ctor_get(v_a_3610_, 7);
lean_inc(v_idx_3621_);
v_generation_3622_ = lean_ctor_get(v_a_3610_, 8);
lean_inc(v_generation_3622_);
v_mt_3623_ = lean_ctor_get(v_a_3610_, 9);
lean_inc(v_mt_3623_);
v_sTerms_3624_ = lean_ctor_get(v_a_3610_, 10);
lean_inc(v_sTerms_3624_);
v_funCC_3625_ = lean_ctor_get_uint8(v_a_3610_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3626_ = lean_ctor_get(v_a_3610_, 11);
lean_inc(v_ematchDiagSource_3626_);
v___x_3627_ = lean_nat_add(v_size_3617_, v___y_3592_);
lean_dec(v___y_3592_);
if (v_hasLambdas_3620_ == 0)
{
v___y_3519_ = v_self_3611_;
v___y_3520_ = v_flipped_3616_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v_ctor_3619_;
v___y_3526_ = v_interpreted_3618_;
v___y_3527_ = v___y_3596_;
v___y_3528_ = v_mt_3623_;
v___y_3529_ = v___y_3599_;
v___y_3530_ = v_a_3610_;
v___y_3531_ = v___x_3627_;
v___y_3532_ = v_congr_3613_;
v___y_3533_ = v___y_3603_;
v___y_3534_ = v___y_3602_;
v___y_3535_ = v_sTerms_3624_;
v___y_3536_ = v___y_3605_;
v___y_3537_ = v_ematchDiagSource_3626_;
v___y_3538_ = v_generation_3622_;
v___y_3539_ = v_idx_3621_;
v___y_3540_ = v___y_3585_;
v___y_3541_ = v___y_3586_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v___y_3590_;
v___y_3544_ = v_target_x3f_3614_;
v___y_3545_ = v___y_3591_;
v___y_3546_ = v_funCC_3625_;
v___y_3547_ = v___y_3593_;
v___y_3548_ = v___y_3607_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3597_;
v___y_3551_ = v_root_3612_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3606_;
v___y_3554_ = v_proof_x3f_3615_;
v___y_3555_ = v___y_3604_;
goto v___jp_3518_;
}
else
{
v___y_3519_ = v_self_3611_;
v___y_3520_ = v_flipped_3616_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3594_;
v___y_3524_ = v___y_3595_;
v___y_3525_ = v_ctor_3619_;
v___y_3526_ = v_interpreted_3618_;
v___y_3527_ = v___y_3596_;
v___y_3528_ = v_mt_3623_;
v___y_3529_ = v___y_3599_;
v___y_3530_ = v_a_3610_;
v___y_3531_ = v___x_3627_;
v___y_3532_ = v_congr_3613_;
v___y_3533_ = v___y_3603_;
v___y_3534_ = v___y_3602_;
v___y_3535_ = v_sTerms_3624_;
v___y_3536_ = v___y_3605_;
v___y_3537_ = v_ematchDiagSource_3626_;
v___y_3538_ = v_generation_3622_;
v___y_3539_ = v_idx_3621_;
v___y_3540_ = v___y_3585_;
v___y_3541_ = v___y_3586_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v___y_3590_;
v___y_3544_ = v_target_x3f_3614_;
v___y_3545_ = v___y_3591_;
v___y_3546_ = v_funCC_3625_;
v___y_3547_ = v___y_3593_;
v___y_3548_ = v___y_3607_;
v___y_3549_ = v___y_3598_;
v___y_3550_ = v___y_3597_;
v___y_3551_ = v_root_3612_;
v___y_3552_ = v___y_3601_;
v___y_3553_ = v___y_3606_;
v___y_3554_ = v_proof_x3f_3615_;
v___y_3555_ = v_hasLambdas_3620_;
goto v___jp_3518_;
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3585_);
lean_dec_ref(v_lhsRoot_3452_);
v_a_3628_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3609_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3609_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
v___jp_3636_:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3646_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec_ref_known(v___x_3659_, 1);
v___x_3660_ = 0;
v___x_3661_ = lean_st_ref_get(v___y_3649_);
v___x_3662_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3661_, v_lhs_3448_, v___x_3660_);
lean_dec(v___x_3661_);
v___x_3663_ = lean_st_ref_get(v___y_3649_);
lean_inc_ref(v___y_3640_);
v___x_3664_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3663_, v___y_3640_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___x_3663_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v_self_3666_; lean_object* v_root_3667_; lean_object* v_congr_3668_; lean_object* v_target_x3f_3669_; lean_object* v_proof_x3f_3670_; uint8_t v_flipped_3671_; lean_object* v_size_3672_; uint8_t v_interpreted_3673_; uint8_t v_ctor_3674_; uint8_t v_hasLambdas_3675_; uint8_t v_heqProofs_3676_; lean_object* v_idx_3677_; lean_object* v_generation_3678_; lean_object* v_mt_3679_; lean_object* v_sTerms_3680_; uint8_t v_funCC_3681_; lean_object* v_ematchDiagSource_3682_; lean_object* v_self_3683_; lean_object* v_next_3684_; uint8_t v_heqProofs_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3693_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v_self_3666_ = lean_ctor_get(v_a_3665_, 0);
lean_inc_ref(v_self_3666_);
v_root_3667_ = lean_ctor_get(v_a_3665_, 2);
lean_inc_ref(v_root_3667_);
v_congr_3668_ = lean_ctor_get(v_a_3665_, 3);
lean_inc_ref(v_congr_3668_);
v_target_x3f_3669_ = lean_ctor_get(v_a_3665_, 4);
lean_inc(v_target_x3f_3669_);
v_proof_x3f_3670_ = lean_ctor_get(v_a_3665_, 5);
lean_inc(v_proof_x3f_3670_);
v_flipped_3671_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12);
v_size_3672_ = lean_ctor_get(v_a_3665_, 6);
lean_inc(v_size_3672_);
v_interpreted_3673_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12 + 1);
v_ctor_3674_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12 + 2);
v_hasLambdas_3675_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12 + 3);
v_heqProofs_3676_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12 + 4);
v_idx_3677_ = lean_ctor_get(v_a_3665_, 7);
lean_inc(v_idx_3677_);
v_generation_3678_ = lean_ctor_get(v_a_3665_, 8);
lean_inc(v_generation_3678_);
v_mt_3679_ = lean_ctor_get(v_a_3665_, 9);
lean_inc(v_mt_3679_);
v_sTerms_3680_ = lean_ctor_get(v_a_3665_, 10);
lean_inc(v_sTerms_3680_);
v_funCC_3681_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3682_ = lean_ctor_get(v_a_3665_, 11);
lean_inc(v_ematchDiagSource_3682_);
lean_dec(v_a_3665_);
v_self_3683_ = lean_ctor_get(v_rhsRoot_3453_, 0);
v_next_3684_ = lean_ctor_get(v_rhsRoot_3453_, 1);
v_heqProofs_3685_ = lean_ctor_get_uint8(v_rhsRoot_3453_, sizeof(void*)*12 + 4);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_rhsRoot_3453_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; lean_object* v_unused_3701_; lean_object* v_unused_3702_; lean_object* v_unused_3703_; 
v_unused_3694_ = lean_ctor_get(v_rhsRoot_3453_, 11);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_rhsRoot_3453_, 10);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_rhsRoot_3453_, 9);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_rhsRoot_3453_, 8);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_rhsRoot_3453_, 7);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_rhsRoot_3453_, 6);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_rhsRoot_3453_, 5);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_rhsRoot_3453_, 4);
lean_dec(v_unused_3701_);
v_unused_3702_ = lean_ctor_get(v_rhsRoot_3453_, 3);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v_rhsRoot_3453_, 2);
lean_dec(v_unused_3703_);
v___x_3687_ = v_rhsRoot_3453_;
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_next_3684_);
lean_inc(v_self_3683_);
lean_dec(v_rhsRoot_3453_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3693_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 11, v_ematchDiagSource_3682_);
lean_ctor_set(v___x_3687_, 10, v_sTerms_3680_);
lean_ctor_set(v___x_3687_, 9, v_mt_3679_);
lean_ctor_set(v___x_3687_, 8, v_generation_3678_);
lean_ctor_set(v___x_3687_, 7, v_idx_3677_);
lean_ctor_set(v___x_3687_, 6, v_size_3672_);
lean_ctor_set(v___x_3687_, 5, v_proof_x3f_3670_);
lean_ctor_set(v___x_3687_, 4, v_target_x3f_3669_);
lean_ctor_set(v___x_3687_, 3, v_congr_3668_);
lean_ctor_set(v___x_3687_, 2, v_root_3667_);
lean_ctor_set(v___x_3687_, 0, v_self_3666_);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_self_3666_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_next_3684_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_root_3667_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_congr_3668_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_target_x3f_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 5, v_proof_x3f_3670_);
lean_ctor_set(v_reuseFailAlloc_3692_, 6, v_size_3672_);
lean_ctor_set(v_reuseFailAlloc_3692_, 7, v_idx_3677_);
lean_ctor_set(v_reuseFailAlloc_3692_, 8, v_generation_3678_);
lean_ctor_set(v_reuseFailAlloc_3692_, 9, v_mt_3679_);
lean_ctor_set(v_reuseFailAlloc_3692_, 10, v_sTerms_3680_);
lean_ctor_set(v_reuseFailAlloc_3692_, 11, v_ematchDiagSource_3682_);
v___x_3690_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; 
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12, v_flipped_3671_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12 + 1, v_interpreted_3673_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12 + 2, v_ctor_3674_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12 + 3, v_hasLambdas_3675_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12 + 4, v_heqProofs_3676_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*12 + 5, v_funCC_3681_);
v___x_3691_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3644_, v___x_3690_, v___y_3649_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_dec_ref_known(v___x_3691_, 1);
if (v_isHEq_3447_ == 0)
{
if (v_heqProofs_3685_ == 0)
{
v___y_3585_ = v___y_3640_;
v___y_3586_ = v___y_3653_;
v___y_3587_ = v___y_3650_;
v___y_3588_ = v___y_3646_;
v___y_3589_ = v___x_3662_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3637_;
v___y_3593_ = v___y_3639_;
v___y_3594_ = v___y_3638_;
v___y_3595_ = v___y_3656_;
v___y_3596_ = v___y_3651_;
v___y_3597_ = v___y_3642_;
v___y_3598_ = v___y_3641_;
v___y_3599_ = v___y_3649_;
v___y_3600_ = v_self_3683_;
v___y_3601_ = v___y_3652_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v___y_3654_;
v___y_3604_ = v___y_3648_;
v___y_3605_ = v___y_3647_;
v___y_3606_ = v___y_3658_;
v___y_3607_ = v___y_3643_;
goto v___jp_3584_;
}
else
{
v___y_3585_ = v___y_3640_;
v___y_3586_ = v___y_3653_;
v___y_3587_ = v___y_3650_;
v___y_3588_ = v___y_3646_;
v___y_3589_ = v___x_3662_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3637_;
v___y_3593_ = v___y_3639_;
v___y_3594_ = v___y_3638_;
v___y_3595_ = v___y_3656_;
v___y_3596_ = v___y_3651_;
v___y_3597_ = v___y_3642_;
v___y_3598_ = v___y_3641_;
v___y_3599_ = v___y_3649_;
v___y_3600_ = v_self_3683_;
v___y_3601_ = v___y_3652_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v___y_3654_;
v___y_3604_ = v___y_3648_;
v___y_3605_ = v___y_3647_;
v___y_3606_ = v___y_3658_;
v___y_3607_ = v_heqProofs_3685_;
goto v___jp_3584_;
}
}
else
{
v___y_3585_ = v___y_3640_;
v___y_3586_ = v___y_3653_;
v___y_3587_ = v___y_3650_;
v___y_3588_ = v___y_3646_;
v___y_3589_ = v___x_3662_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3637_;
v___y_3593_ = v___y_3639_;
v___y_3594_ = v___y_3638_;
v___y_3595_ = v___y_3656_;
v___y_3596_ = v___y_3651_;
v___y_3597_ = v___y_3642_;
v___y_3598_ = v___y_3641_;
v___y_3599_ = v___y_3649_;
v___y_3600_ = v_self_3683_;
v___y_3601_ = v___y_3652_;
v___y_3602_ = v___y_3645_;
v___y_3603_ = v___y_3654_;
v___y_3604_ = v___y_3648_;
v___y_3605_ = v___y_3647_;
v___y_3606_ = v___y_3658_;
v___y_3607_ = v_isHEq_3447_;
goto v___jp_3584_;
}
}
else
{
lean_dec_ref(v_self_3683_);
lean_dec(v___x_3662_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v_lhsRoot_3452_);
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v___x_3662_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
v_a_3704_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3664_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3664_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec_ref(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
return v___x_3659_;
}
}
v___jp_3717_:
{
lean_object* v_self_3733_; lean_object* v_next_3734_; lean_object* v_size_3735_; uint8_t v_hasLambdas_3736_; uint8_t v_heqProofs_3737_; lean_object* v___x_3738_; 
v_self_3733_ = lean_ctor_get(v_lhsRoot_3452_, 0);
v_next_3734_ = lean_ctor_get(v_lhsRoot_3452_, 1);
v_size_3735_ = lean_ctor_get(v_lhsRoot_3452_, 6);
v_hasLambdas_3736_ = lean_ctor_get_uint8(v_lhsRoot_3452_, sizeof(void*)*12 + 3);
v_heqProofs_3737_ = lean_ctor_get_uint8(v_lhsRoot_3452_, sizeof(void*)*12 + 4);
v___x_3738_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3733_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v_root_3740_; lean_object* v___x_3741_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v_root_3740_ = lean_ctor_get(v_rhsNode_3451_, 2);
lean_inc_ref_n(v_root_3740_, 2);
lean_dec_ref(v_rhsNode_3451_);
lean_inc_ref(v_lhs_3448_);
v___x_3741_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3448_, v_root_3740_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_toCold_3742_; lean_object* v_options_3743_; uint8_t v_hasTrace_3744_; 
lean_dec_ref_known(v___x_3741_, 1);
v_toCold_3742_ = lean_ctor_get(v___y_3731_, 0);
v_options_3743_ = lean_ctor_get(v_toCold_3742_, 2);
v_hasTrace_3744_ = lean_ctor_get_uint8(v_options_3743_, sizeof(void*)*1);
if (v_hasTrace_3744_ == 0)
{
lean_inc_ref(v_self_3733_);
lean_inc_ref(v_next_3734_);
lean_inc(v_size_3735_);
v___y_3637_ = v_size_3735_;
v___y_3638_ = v_next_3734_;
v___y_3639_ = v___y_3718_;
v___y_3640_ = v_self_3733_;
v___y_3641_ = v_fns_u2082_3722_;
v___y_3642_ = v___y_3719_;
v___y_3643_ = v_heqProofs_3737_;
v___y_3644_ = v___y_3720_;
v___y_3645_ = v___y_3721_;
v___y_3646_ = v_a_3739_;
v___y_3647_ = v_root_3740_;
v___y_3648_ = v_hasLambdas_3736_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
v___y_3656_ = v___y_3730_;
v___y_3657_ = v___y_3731_;
v___y_3658_ = v___y_3732_;
goto v___jp_3636_;
}
else
{
lean_object* v_inheritedTraceOptions_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_inheritedTraceOptions_3745_ = lean_ctor_get(v_toCold_3742_, 11);
v___x_3746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3745_, v_options_3743_, v___x_3746_);
if (v___x_3747_ == 0)
{
lean_inc_ref(v_self_3733_);
lean_inc_ref(v_next_3734_);
lean_inc(v_size_3735_);
v___y_3637_ = v_size_3735_;
v___y_3638_ = v_next_3734_;
v___y_3639_ = v___y_3718_;
v___y_3640_ = v_self_3733_;
v___y_3641_ = v_fns_u2082_3722_;
v___y_3642_ = v___y_3719_;
v___y_3643_ = v_heqProofs_3737_;
v___y_3644_ = v___y_3720_;
v___y_3645_ = v___y_3721_;
v___y_3646_ = v_a_3739_;
v___y_3647_ = v_root_3740_;
v___y_3648_ = v_hasLambdas_3736_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
v___y_3656_ = v___y_3730_;
v___y_3657_ = v___y_3731_;
v___y_3658_ = v___y_3732_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Meta_Grind_updateLastTag(v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3749_; 
lean_dec_ref_known(v___x_3748_, 1);
lean_inc_ref(v_lhs_3448_);
v___x_3749_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3448_, v___y_3723_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3751_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
lean_inc_ref(v_root_3740_);
v___x_3751_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3740_, v___y_3723_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = lean_st_ref_get(v___y_3723_);
lean_inc_ref(v_lhs_3448_);
v___x_3754_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3753_, v_lhs_3448_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___x_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3755_, v___y_3723_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v_a_3750_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v_a_3752_);
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set(v___x_3763_, 1, v_a_3757_);
v___x_3764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3716_, v___x_3763_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_dec_ref_known(v___x_3764_, 1);
lean_inc_ref(v_self_3733_);
lean_inc_ref(v_next_3734_);
lean_inc(v_size_3735_);
v___y_3637_ = v_size_3735_;
v___y_3638_ = v_next_3734_;
v___y_3639_ = v___y_3718_;
v___y_3640_ = v_self_3733_;
v___y_3641_ = v_fns_u2082_3722_;
v___y_3642_ = v___y_3719_;
v___y_3643_ = v_heqProofs_3737_;
v___y_3644_ = v___y_3720_;
v___y_3645_ = v___y_3721_;
v___y_3646_ = v_a_3739_;
v___y_3647_ = v_root_3740_;
v___y_3648_ = v_hasLambdas_3736_;
v___y_3649_ = v___y_3723_;
v___y_3650_ = v___y_3724_;
v___y_3651_ = v___y_3725_;
v___y_3652_ = v___y_3726_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3728_;
v___y_3655_ = v___y_3729_;
v___y_3656_ = v___y_3730_;
v___y_3657_ = v___y_3731_;
v___y_3658_ = v___y_3732_;
goto v___jp_3636_;
}
else
{
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
return v___x_3764_;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec(v_a_3752_);
lean_dec(v_a_3750_);
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
v_a_3765_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3756_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3756_);
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
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec(v_a_3752_);
lean_dec(v_a_3750_);
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
v_a_3773_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3754_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3754_);
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
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_a_3750_);
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
v_a_3781_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3751_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3751_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
v_a_3789_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3749_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3749_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
return v___x_3748_;
}
}
}
}
else
{
lean_dec_ref(v_root_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_lhs_3448_);
return v___x_3741_;
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_fns_u2082_3722_);
lean_dec_ref(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
v_a_3797_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3738_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3738_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
v___jp_3805_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = lean_array_get_size(v___y_3806_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = lean_nat_dec_eq(v___x_3820_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v_self_3823_; lean_object* v___x_3824_; 
v_self_3823_ = lean_ctor_get(v_lhsRoot_3452_, 0);
lean_inc_ref(v_self_3823_);
v___x_3824_ = l_Lean_Meta_Grind_getFnRoots(v_self_3823_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___y_3718_ = v___y_3806_;
v___y_3719_ = v___y_3807_;
v___y_3720_ = v___y_3808_;
v___y_3721_ = v_fns_u2081_3809_;
v_fns_u2082_3722_ = v_a_3825_;
v___y_3723_ = v___y_3810_;
v___y_3724_ = v___y_3811_;
v___y_3725_ = v___y_3812_;
v___y_3726_ = v___y_3813_;
v___y_3727_ = v___y_3814_;
v___y_3728_ = v___y_3815_;
v___y_3729_ = v___y_3816_;
v___y_3730_ = v___y_3817_;
v___y_3731_ = v___y_3818_;
v___y_3732_ = v___y_3819_;
goto v___jp_3717_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_fns_u2081_3809_);
lean_dec_ref(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
v_a_3826_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3824_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3824_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3834_; 
v___x_3834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3718_ = v___y_3806_;
v___y_3719_ = v___y_3807_;
v___y_3720_ = v___y_3808_;
v___y_3721_ = v_fns_u2081_3809_;
v_fns_u2082_3722_ = v___x_3834_;
v___y_3723_ = v___y_3810_;
v___y_3724_ = v___y_3811_;
v___y_3725_ = v___y_3812_;
v___y_3726_ = v___y_3813_;
v___y_3727_ = v___y_3814_;
v___y_3728_ = v___y_3815_;
v___y_3729_ = v___y_3816_;
v___y_3730_ = v___y_3817_;
v___y_3731_ = v___y_3818_;
v___y_3732_ = v___y_3819_;
goto v___jp_3717_;
}
}
v___jp_3835_:
{
lean_object* v___x_3846_; 
lean_inc_ref(v_lhs_3448_);
v___x_3846_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3448_, v___y_3836_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3914_; 
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; 
v_unused_3915_ = lean_ctor_get(v___x_3846_, 0);
lean_dec(v_unused_3915_);
v___x_3848_ = v___x_3846_;
v_isShared_3849_ = v_isSharedCheck_3914_;
goto v_resetjp_3847_;
}
else
{
lean_dec(v___x_3846_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3914_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_self_3850_; lean_object* v_next_3851_; lean_object* v_root_3852_; lean_object* v_congr_3853_; lean_object* v_size_3854_; uint8_t v_interpreted_3855_; uint8_t v_ctor_3856_; uint8_t v_hasLambdas_3857_; uint8_t v_heqProofs_3858_; lean_object* v_idx_3859_; lean_object* v_generation_3860_; lean_object* v_mt_3861_; lean_object* v_sTerms_3862_; uint8_t v_funCC_3863_; lean_object* v_ematchDiagSource_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3911_; 
v_self_3850_ = lean_ctor_get(v_lhsNode_3450_, 0);
v_next_3851_ = lean_ctor_get(v_lhsNode_3450_, 1);
v_root_3852_ = lean_ctor_get(v_lhsNode_3450_, 2);
v_congr_3853_ = lean_ctor_get(v_lhsNode_3450_, 3);
v_size_3854_ = lean_ctor_get(v_lhsNode_3450_, 6);
v_interpreted_3855_ = lean_ctor_get_uint8(v_lhsNode_3450_, sizeof(void*)*12 + 1);
v_ctor_3856_ = lean_ctor_get_uint8(v_lhsNode_3450_, sizeof(void*)*12 + 2);
v_hasLambdas_3857_ = lean_ctor_get_uint8(v_lhsNode_3450_, sizeof(void*)*12 + 3);
v_heqProofs_3858_ = lean_ctor_get_uint8(v_lhsNode_3450_, sizeof(void*)*12 + 4);
v_idx_3859_ = lean_ctor_get(v_lhsNode_3450_, 7);
v_generation_3860_ = lean_ctor_get(v_lhsNode_3450_, 8);
v_mt_3861_ = lean_ctor_get(v_lhsNode_3450_, 9);
v_sTerms_3862_ = lean_ctor_get(v_lhsNode_3450_, 10);
v_funCC_3863_ = lean_ctor_get_uint8(v_lhsNode_3450_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3864_ = lean_ctor_get(v_lhsNode_3450_, 11);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_lhsNode_3450_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; lean_object* v_unused_3913_; 
v_unused_3912_ = lean_ctor_get(v_lhsNode_3450_, 5);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_lhsNode_3450_, 4);
lean_dec(v_unused_3913_);
v___x_3866_ = v_lhsNode_3450_;
v_isShared_3867_ = v_isSharedCheck_3911_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_ematchDiagSource_3864_);
lean_inc(v_sTerms_3862_);
lean_inc(v_mt_3861_);
lean_inc(v_generation_3860_);
lean_inc(v_idx_3859_);
lean_inc(v_size_3854_);
lean_inc(v_congr_3853_);
lean_inc(v_root_3852_);
lean_inc(v_next_3851_);
lean_inc(v_self_3850_);
lean_dec(v_lhsNode_3450_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3911_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3849_ == 0)
{
lean_ctor_set_tag(v___x_3848_, 1);
lean_ctor_set(v___x_3848_, 0, v_rhs_3449_);
v___x_3869_ = v___x_3848_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_rhs_3449_);
v___x_3869_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_proof_3446_);
lean_inc_ref(v_root_3852_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 5, v___x_3870_);
lean_ctor_set(v___x_3866_, 4, v___x_3869_);
v___x_3872_ = v___x_3866_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_self_3850_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_next_3851_);
lean_ctor_set(v_reuseFailAlloc_3909_, 2, v_root_3852_);
lean_ctor_set(v_reuseFailAlloc_3909_, 3, v_congr_3853_);
lean_ctor_set(v_reuseFailAlloc_3909_, 4, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3909_, 5, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3909_, 6, v_size_3854_);
lean_ctor_set(v_reuseFailAlloc_3909_, 7, v_idx_3859_);
lean_ctor_set(v_reuseFailAlloc_3909_, 8, v_generation_3860_);
lean_ctor_set(v_reuseFailAlloc_3909_, 9, v_mt_3861_);
lean_ctor_set(v_reuseFailAlloc_3909_, 10, v_sTerms_3862_);
lean_ctor_set(v_reuseFailAlloc_3909_, 11, v_ematchDiagSource_3864_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*12 + 1, v_interpreted_3855_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*12 + 2, v_ctor_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*12 + 3, v_hasLambdas_3857_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*12 + 4, v_heqProofs_3858_);
lean_ctor_set_uint8(v_reuseFailAlloc_3909_, sizeof(void*)*12 + 5, v_funCC_3863_);
v___x_3872_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3873_; 
lean_ctor_set_uint8(v___x_3872_, sizeof(void*)*12, v_flipped_3454_);
lean_inc_ref(v_lhs_3448_);
v___x_3873_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3448_, v___x_3872_, v___y_3836_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v___x_3874_; 
lean_dec_ref_known(v___x_3873_, 1);
v___x_3874_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3452_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3453_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = lean_array_get_size(v_a_3875_);
v___x_3879_ = lean_unsigned_to_nat(0u);
v___x_3880_ = lean_nat_dec_eq(v___x_3878_, v___x_3879_);
if (v___x_3880_ == 0)
{
lean_object* v_self_3881_; lean_object* v___x_3882_; 
v_self_3881_ = lean_ctor_get(v_rhsRoot_3453_, 0);
lean_inc_ref(v_self_3881_);
v___x_3882_ = l_Lean_Meta_Grind_getFnRoots(v_self_3881_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___y_3806_ = v_a_3877_;
v___y_3807_ = v_a_3875_;
v___y_3808_ = v_root_3852_;
v_fns_u2081_3809_ = v_a_3883_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___y_3839_;
v___y_3814_ = v___y_3840_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3842_;
v___y_3817_ = v___y_3843_;
v___y_3818_ = v___y_3844_;
v___y_3819_ = v___y_3845_;
goto v___jp_3805_;
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3877_);
lean_dec(v_a_3875_);
lean_dec_ref(v_root_3852_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
v_a_3884_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3882_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3882_);
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
lean_object* v___x_3892_; 
v___x_3892_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3806_ = v_a_3877_;
v___y_3807_ = v_a_3875_;
v___y_3808_ = v_root_3852_;
v_fns_u2081_3809_ = v___x_3892_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___y_3839_;
v___y_3814_ = v___y_3840_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3842_;
v___y_3817_ = v___y_3843_;
v___y_3818_ = v___y_3844_;
v___y_3819_ = v___y_3845_;
goto v___jp_3805_;
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v_a_3875_);
lean_dec_ref(v_root_3852_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
v_a_3893_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3876_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3876_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v_root_3852_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
v_a_3901_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3874_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3874_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_dec_ref(v_root_3852_);
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhs_3448_);
return v___x_3873_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3453_);
lean_dec_ref(v_lhsRoot_3452_);
lean_dec_ref(v_rhsNode_3451_);
lean_dec_ref(v_lhsNode_3450_);
lean_dec_ref(v_rhs_3449_);
lean_dec_ref(v_lhs_3448_);
lean_dec_ref(v_proof_3446_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3945_ = _args[0];
lean_object* v_isHEq_3946_ = _args[1];
lean_object* v_lhs_3947_ = _args[2];
lean_object* v_rhs_3948_ = _args[3];
lean_object* v_lhsNode_3949_ = _args[4];
lean_object* v_rhsNode_3950_ = _args[5];
lean_object* v_lhsRoot_3951_ = _args[6];
lean_object* v_rhsRoot_3952_ = _args[7];
lean_object* v_flipped_3953_ = _args[8];
lean_object* v_a_3954_ = _args[9];
lean_object* v_a_3955_ = _args[10];
lean_object* v_a_3956_ = _args[11];
lean_object* v_a_3957_ = _args[12];
lean_object* v_a_3958_ = _args[13];
lean_object* v_a_3959_ = _args[14];
lean_object* v_a_3960_ = _args[15];
lean_object* v_a_3961_ = _args[16];
lean_object* v_a_3962_ = _args[17];
lean_object* v_a_3963_ = _args[18];
lean_object* v_a_3964_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3965_; uint8_t v_flipped_boxed_3966_; lean_object* v_res_3967_; 
v_isHEq_boxed_3965_ = lean_unbox(v_isHEq_3946_);
v_flipped_boxed_3966_ = lean_unbox(v_flipped_3953_);
v_res_3967_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3945_, v_isHEq_boxed_3965_, v_lhs_3947_, v_rhs_3948_, v_lhsNode_3949_, v_rhsNode_3950_, v_lhsRoot_3951_, v_rhsRoot_3952_, v_flipped_boxed_3966_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec(v_a_3954_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3968_, lean_object* v_as_x27_3969_, lean_object* v_b_3970_, lean_object* v_a_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3969_, v_b_3970_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3984_, lean_object* v_as_x27_3985_, lean_object* v_b_3986_, lean_object* v_a_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3984_, v_as_x27_3985_, v_b_3986_, v_a_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec(v_as_x27_3985_);
lean_dec(v_as_3984_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_4000_, lean_object* v_as_x27_4001_, lean_object* v_b_4002_, lean_object* v_a_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_4001_, v_b_4002_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4016_, lean_object* v_as_x27_4017_, lean_object* v_b_4018_, lean_object* v_a_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4016_, v_as_x27_4017_, v_b_4018_, v_a_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec(v_as_x27_4017_);
lean_dec(v_as_4016_);
return v_res_4031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4034_ = l_Lean_stringToMessageData(v___x_4033_);
return v___x_4034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4040_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4041_ = l_Lean_Name_append(v___x_4040_, v___x_4039_);
return v___x_4041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4044_ = l_Lean_stringToMessageData(v___x_4043_);
return v___x_4044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4047_ = l_Lean_stringToMessageData(v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4048_, lean_object* v_rhs_4049_, lean_object* v_proof_4050_, uint8_t v_isHEq_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = lean_st_ref_get(v_a_4052_);
lean_inc_ref(v_lhs_4048_);
v___x_4067_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4066_, v_lhs_4048_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v___x_4066_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = lean_st_ref_get(v_a_4052_);
lean_inc_ref(v_rhs_4049_);
v___x_4070_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4069_, v_rhs_4049_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v___x_4069_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v_root_4072_; lean_object* v_root_4073_; size_t v___x_4074_; size_t v___x_4075_; uint8_t v___x_4076_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v_root_4072_ = lean_ctor_get(v_a_4068_, 2);
v_root_4073_ = lean_ctor_get(v_a_4071_, 2);
v___x_4074_ = lean_ptr_addr(v_root_4072_);
v___x_4075_ = lean_ptr_addr(v_root_4073_);
v___x_4076_ = lean_usize_dec_eq(v___x_4074_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v_toCold_4077_; lean_object* v_options_4078_; lean_object* v_inheritedTraceOptions_4079_; uint8_t v_hasTrace_4080_; uint8_t v___x_4081_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4119_; uint8_t v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; uint8_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4177_; uint8_t v___y_4178_; uint8_t v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; uint8_t v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; uint8_t v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; uint8_t v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v_size_4236_; uint8_t v_interpreted_4237_; uint8_t v_ctor_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4245_; uint8_t v_ctor_4246_; uint8_t v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4267_; lean_object* v___y_4268_; uint8_t v_valueInconsistency_4269_; uint8_t v_trueEqFalse_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; 
v_toCold_4077_ = lean_ctor_get(v_a_4060_, 0);
v_options_4078_ = lean_ctor_get(v_toCold_4077_, 2);
v_inheritedTraceOptions_4079_ = lean_ctor_get(v_toCold_4077_, 11);
v_hasTrace_4080_ = lean_ctor_get_uint8(v_options_4078_, sizeof(void*)*1);
v___x_4081_ = 1;
if (v_hasTrace_4080_ == 0)
{
v___y_4326_ = v_a_4052_;
v___y_4327_ = v_a_4053_;
v___y_4328_ = v_a_4054_;
v___y_4329_ = v_a_4055_;
v___y_4330_ = v_a_4056_;
v___y_4331_ = v_a_4057_;
v___y_4332_ = v_a_4058_;
v___y_4333_ = v_a_4059_;
v___y_4334_ = v_a_4060_;
v___y_4335_ = v_a_4061_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4369_; lean_object* v_____do__lift_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___x_4384_; uint8_t v___x_4385_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4079_, v_options_4078_, v___x_4384_);
if (v___x_4385_ == 0)
{
v___y_4326_ = v_a_4052_;
v___y_4327_ = v_a_4053_;
v___y_4328_ = v_a_4054_;
v___y_4329_ = v_a_4055_;
v___y_4330_ = v_a_4056_;
v___y_4331_ = v_a_4057_;
v___y_4332_ = v_a_4058_;
v___y_4333_ = v_a_4059_;
v___y_4334_ = v_a_4060_;
v___y_4335_ = v_a_4061_;
goto v___jp_4325_;
}
else
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Meta_Grind_updateLastTag(v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_dec_ref_known(v___x_4386_, 1);
if (v_isHEq_4051_ == 0)
{
lean_object* v___x_4387_; 
lean_inc_ref(v_rhs_4049_);
lean_inc_ref(v_lhs_4048_);
v___x_4387_ = l_Lean_Meta_mkEq(v_lhs_4048_, v_rhs_4049_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v_____do__lift_4371_ = v_a_4388_;
v___y_4372_ = v_a_4052_;
v___y_4373_ = v_a_4053_;
v___y_4374_ = v_a_4054_;
v___y_4375_ = v_a_4055_;
v___y_4376_ = v_a_4056_;
v___y_4377_ = v_a_4057_;
v___y_4378_ = v_a_4058_;
v___y_4379_ = v_a_4059_;
v___y_4380_ = v_a_4060_;
v___y_4381_ = v_a_4061_;
goto v___jp_4370_;
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4389_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4387_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4387_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
else
{
lean_object* v___x_4397_; 
lean_inc_ref(v_rhs_4049_);
lean_inc_ref(v_lhs_4048_);
v___x_4397_ = l_Lean_Meta_mkHEq(v_lhs_4048_, v_rhs_4049_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v_____do__lift_4371_ = v_a_4398_;
v___y_4372_ = v_a_4052_;
v___y_4373_ = v_a_4053_;
v___y_4374_ = v_a_4054_;
v___y_4375_ = v_a_4055_;
v___y_4376_ = v_a_4056_;
v___y_4377_ = v_a_4057_;
v___y_4378_ = v_a_4058_;
v___y_4379_ = v_a_4059_;
v___y_4380_ = v_a_4060_;
v___y_4381_ = v_a_4061_;
goto v___jp_4370_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4399_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4397_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4397_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
else
{
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
return v___x_4386_;
}
}
v___jp_4370_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = l_Lean_MessageData_ofExpr(v_____do__lift_4371_);
v___x_4383_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4369_, v___x_4382_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_dec_ref_known(v___x_4383_, 1);
v___y_4326_ = v___y_4372_;
v___y_4327_ = v___y_4373_;
v___y_4328_ = v___y_4374_;
v___y_4329_ = v___y_4375_;
v___y_4330_ = v___y_4376_;
v___y_4331_ = v___y_4377_;
v___y_4332_ = v___y_4378_;
v___y_4333_ = v___y_4379_;
v___y_4334_ = v___y_4380_;
v___y_4335_ = v___y_4381_;
goto v___jp_4325_;
}
else
{
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
return v___x_4383_;
}
}
}
v___jp_4082_:
{
lean_object* v_toCold_4093_; lean_object* v_options_4094_; uint8_t v_hasTrace_4095_; 
v_toCold_4093_ = lean_ctor_get(v___y_4091_, 0);
v_options_4094_ = lean_ctor_get(v_toCold_4093_, 2);
v_hasTrace_4095_ = lean_ctor_get_uint8(v_options_4094_, sizeof(void*)*1);
if (v_hasTrace_4095_ == 0)
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Meta_Grind_checkInvariants(v___x_4076_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4096_;
}
else
{
lean_object* v_inheritedTraceOptions_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
v_inheritedTraceOptions_4097_ = lean_ctor_get(v_toCold_4093_, 11);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4100_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_Meta_Grind_checkInvariants(v___x_4076_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_Grind_updateLastTag(v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_dec_ref_known(v___x_4102_, 1);
v___x_4103_ = lean_st_ref_get(v___y_4083_);
v___x_4104_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4103_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___x_4103_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
v___x_4106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v_a_4105_);
v___x_4108_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4098_, v___x_4107_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4109_; 
lean_dec_ref_known(v___x_4108_, 1);
v___x_4109_ = l_Lean_Meta_Grind_checkInvariants(v___x_4076_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4109_;
}
else
{
return v___x_4108_;
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_a_4110_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4104_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4104_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
else
{
return v___x_4102_;
}
}
}
}
v___jp_4118_:
{
lean_object* v___x_4132_; 
v___x_4132_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4122_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; uint8_t v___x_4134_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = lean_unbox(v_a_4133_);
lean_dec(v_a_4133_);
if (v___x_4134_ == 0)
{
if (v___y_4120_ == 0)
{
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___y_4119_);
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
v___y_4090_ = v___y_4129_;
v___y_4091_ = v___y_4130_;
v___y_4092_ = v___y_4131_;
goto v___jp_4082_;
}
else
{
lean_object* v_self_4135_; lean_object* v_self_4136_; lean_object* v___x_4137_; 
v_self_4135_ = lean_ctor_get(v___y_4119_, 0);
lean_inc_ref(v_self_4135_);
lean_dec_ref(v___y_4119_);
v_self_4136_ = lean_ctor_get(v___y_4121_, 0);
lean_inc_ref(v_self_4136_);
lean_dec_ref(v___y_4121_);
v___x_4137_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4135_, v_self_4136_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_dec_ref_known(v___x_4137_, 1);
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
v___y_4090_ = v___y_4129_;
v___y_4091_ = v___y_4130_;
v___y_4092_ = v___y_4131_;
goto v___jp_4082_;
}
else
{
return v___x_4137_;
}
}
}
else
{
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___y_4119_);
v___y_4083_ = v___y_4122_;
v___y_4084_ = v___y_4123_;
v___y_4085_ = v___y_4124_;
v___y_4086_ = v___y_4125_;
v___y_4087_ = v___y_4126_;
v___y_4088_ = v___y_4127_;
v___y_4089_ = v___y_4128_;
v___y_4090_ = v___y_4129_;
v___y_4091_ = v___y_4130_;
v___y_4092_ = v___y_4131_;
goto v___jp_4082_;
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___y_4119_);
v_a_4138_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4132_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4132_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
v___jp_4146_:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4150_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; uint8_t v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = lean_unbox(v_a_4161_);
lean_dec(v_a_4161_);
if (v___x_4162_ == 0)
{
uint8_t v_ctor_4163_; 
v_ctor_4163_ = lean_ctor_get_uint8(v___y_4148_, sizeof(void*)*12 + 2);
if (v_ctor_4163_ == 0)
{
v___y_4119_ = v___y_4148_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
goto v___jp_4118_;
}
else
{
uint8_t v_ctor_4164_; 
v_ctor_4164_ = lean_ctor_get_uint8(v___y_4149_, sizeof(void*)*12 + 2);
if (v_ctor_4164_ == 0)
{
v___y_4119_ = v___y_4148_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
goto v___jp_4118_;
}
else
{
lean_object* v_self_4165_; lean_object* v_self_4166_; lean_object* v___x_4167_; 
v_self_4165_ = lean_ctor_get(v___y_4148_, 0);
v_self_4166_ = lean_ctor_get(v___y_4149_, 0);
lean_inc_ref(v_self_4166_);
lean_inc_ref(v_self_4165_);
v___x_4167_ = l_Lean_Meta_Grind_propagateCtor(v_self_4165_, v_self_4166_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_dec_ref_known(v___x_4167_, 1);
v___y_4119_ = v___y_4148_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
goto v___jp_4118_;
}
else
{
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v___x_4167_;
}
}
}
}
else
{
v___y_4119_ = v___y_4148_;
v___y_4120_ = v___y_4147_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
goto v___jp_4118_;
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4148_);
v_a_4168_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4160_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4160_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
v___jp_4176_:
{
if (v___y_4179_ == 0)
{
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4177_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
v___y_4151_ = v___y_4182_;
v___y_4152_ = v___y_4183_;
v___y_4153_ = v___y_4184_;
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___y_4186_;
v___y_4156_ = v___y_4187_;
v___y_4157_ = v___y_4188_;
v___y_4158_ = v___y_4189_;
v___y_4159_ = v___y_4190_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_dec_ref_known(v___x_4191_, 1);
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4177_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___y_4181_;
v___y_4151_ = v___y_4182_;
v___y_4152_ = v___y_4183_;
v___y_4153_ = v___y_4184_;
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___y_4186_;
v___y_4156_ = v___y_4187_;
v___y_4157_ = v___y_4188_;
v___y_4158_ = v___y_4189_;
v___y_4159_ = v___y_4190_;
goto v___jp_4146_;
}
else
{
lean_dec_ref(v___y_4180_);
lean_dec_ref(v___y_4177_);
return v___x_4191_;
}
}
}
v___jp_4192_:
{
lean_object* v___x_4207_; 
lean_inc_ref(v___y_4194_);
lean_inc_ref(v___y_4203_);
v___x_4207_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4050_, v_isHEq_4051_, v_rhs_4049_, v_lhs_4048_, v_a_4071_, v_a_4068_, v___y_4203_, v___y_4194_, v___x_4081_, v___y_4206_, v___y_4198_, v___y_4195_, v___y_4202_, v___y_4205_, v___y_4204_, v___y_4201_, v___y_4200_, v___y_4199_, v___y_4196_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_dec_ref_known(v___x_4207_, 1);
v___y_4177_ = v___y_4194_;
v___y_4178_ = v___y_4193_;
v___y_4179_ = v___y_4197_;
v___y_4180_ = v___y_4203_;
v___y_4181_ = v___y_4206_;
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4195_;
v___y_4184_ = v___y_4202_;
v___y_4185_ = v___y_4205_;
v___y_4186_ = v___y_4204_;
v___y_4187_ = v___y_4201_;
v___y_4188_ = v___y_4200_;
v___y_4189_ = v___y_4199_;
v___y_4190_ = v___y_4196_;
goto v___jp_4176_;
}
else
{
lean_dec_ref(v___y_4203_);
lean_dec_ref(v___y_4194_);
return v___x_4207_;
}
}
v___jp_4208_:
{
lean_object* v___x_4223_; 
lean_inc_ref(v___y_4219_);
lean_inc_ref(v___y_4210_);
v___x_4223_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4050_, v_isHEq_4051_, v_lhs_4048_, v_rhs_4049_, v_a_4068_, v_a_4071_, v___y_4210_, v___y_4219_, v___x_4076_, v___y_4222_, v___y_4214_, v___y_4211_, v___y_4218_, v___y_4221_, v___y_4220_, v___y_4217_, v___y_4216_, v___y_4215_, v___y_4212_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_dec_ref_known(v___x_4223_, 1);
v___y_4177_ = v___y_4210_;
v___y_4178_ = v___y_4209_;
v___y_4179_ = v___y_4213_;
v___y_4180_ = v___y_4219_;
v___y_4181_ = v___y_4222_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4211_;
v___y_4184_ = v___y_4218_;
v___y_4185_ = v___y_4221_;
v___y_4186_ = v___y_4220_;
v___y_4187_ = v___y_4217_;
v___y_4188_ = v___y_4216_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___y_4212_;
goto v___jp_4176_;
}
else
{
lean_dec_ref(v___y_4219_);
lean_dec_ref(v___y_4210_);
return v___x_4223_;
}
}
v___jp_4224_:
{
lean_object* v_size_4242_; uint8_t v___x_4243_; 
v_size_4242_ = lean_ctor_get(v___y_4225_, 6);
v___x_4243_ = lean_nat_dec_lt(v_size_4236_, v_size_4242_);
lean_dec(v_size_4236_);
if (v___x_4243_ == 0)
{
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___y_4225_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4231_;
v___y_4216_ = v___y_4232_;
v___y_4217_ = v___y_4233_;
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___y_4235_;
v___y_4220_ = v___y_4239_;
v___y_4221_ = v___y_4240_;
v___y_4222_ = v___y_4241_;
goto v___jp_4208_;
}
else
{
if (v_interpreted_4237_ == 0)
{
if (v_ctor_4238_ == 0)
{
v___y_4193_ = v___y_4226_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4227_;
v___y_4196_ = v___y_4228_;
v___y_4197_ = v___y_4229_;
v___y_4198_ = v___y_4230_;
v___y_4199_ = v___y_4231_;
v___y_4200_ = v___y_4232_;
v___y_4201_ = v___y_4233_;
v___y_4202_ = v___y_4234_;
v___y_4203_ = v___y_4235_;
v___y_4204_ = v___y_4239_;
v___y_4205_ = v___y_4240_;
v___y_4206_ = v___y_4241_;
goto v___jp_4192_;
}
else
{
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___y_4225_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4231_;
v___y_4216_ = v___y_4232_;
v___y_4217_ = v___y_4233_;
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___y_4235_;
v___y_4220_ = v___y_4239_;
v___y_4221_ = v___y_4240_;
v___y_4222_ = v___y_4241_;
goto v___jp_4208_;
}
}
else
{
v___y_4209_ = v___y_4226_;
v___y_4210_ = v___y_4225_;
v___y_4211_ = v___y_4227_;
v___y_4212_ = v___y_4228_;
v___y_4213_ = v___y_4229_;
v___y_4214_ = v___y_4230_;
v___y_4215_ = v___y_4231_;
v___y_4216_ = v___y_4232_;
v___y_4217_ = v___y_4233_;
v___y_4218_ = v___y_4234_;
v___y_4219_ = v___y_4235_;
v___y_4220_ = v___y_4239_;
v___y_4221_ = v___y_4240_;
v___y_4222_ = v___y_4241_;
goto v___jp_4208_;
}
}
}
v___jp_4244_:
{
if (v_ctor_4246_ == 0)
{
lean_object* v_size_4260_; uint8_t v_interpreted_4261_; uint8_t v_ctor_4262_; 
v_size_4260_ = lean_ctor_get(v___y_4256_, 6);
lean_inc(v_size_4260_);
v_interpreted_4261_ = lean_ctor_get_uint8(v___y_4256_, sizeof(void*)*12 + 1);
v_ctor_4262_ = lean_ctor_get_uint8(v___y_4256_, sizeof(void*)*12 + 2);
v___y_4225_ = v___y_4245_;
v___y_4226_ = v___y_4247_;
v___y_4227_ = v___y_4248_;
v___y_4228_ = v___y_4249_;
v___y_4229_ = v___y_4250_;
v___y_4230_ = v___y_4251_;
v___y_4231_ = v___y_4252_;
v___y_4232_ = v___y_4253_;
v___y_4233_ = v___y_4254_;
v___y_4234_ = v___y_4255_;
v___y_4235_ = v___y_4256_;
v_size_4236_ = v_size_4260_;
v_interpreted_4237_ = v_interpreted_4261_;
v_ctor_4238_ = v_ctor_4262_;
v___y_4239_ = v___y_4257_;
v___y_4240_ = v___y_4258_;
v___y_4241_ = v___y_4259_;
goto v___jp_4224_;
}
else
{
uint8_t v_ctor_4263_; 
v_ctor_4263_ = lean_ctor_get_uint8(v___y_4256_, sizeof(void*)*12 + 2);
if (v_ctor_4263_ == 0)
{
v___y_4193_ = v___y_4247_;
v___y_4194_ = v___y_4245_;
v___y_4195_ = v___y_4248_;
v___y_4196_ = v___y_4249_;
v___y_4197_ = v___y_4250_;
v___y_4198_ = v___y_4251_;
v___y_4199_ = v___y_4252_;
v___y_4200_ = v___y_4253_;
v___y_4201_ = v___y_4254_;
v___y_4202_ = v___y_4255_;
v___y_4203_ = v___y_4256_;
v___y_4204_ = v___y_4257_;
v___y_4205_ = v___y_4258_;
v___y_4206_ = v___y_4259_;
goto v___jp_4192_;
}
else
{
lean_object* v_size_4264_; uint8_t v_interpreted_4265_; 
v_size_4264_ = lean_ctor_get(v___y_4256_, 6);
lean_inc(v_size_4264_);
v_interpreted_4265_ = lean_ctor_get_uint8(v___y_4256_, sizeof(void*)*12 + 1);
v___y_4225_ = v___y_4245_;
v___y_4226_ = v___y_4247_;
v___y_4227_ = v___y_4248_;
v___y_4228_ = v___y_4249_;
v___y_4229_ = v___y_4250_;
v___y_4230_ = v___y_4251_;
v___y_4231_ = v___y_4252_;
v___y_4232_ = v___y_4253_;
v___y_4233_ = v___y_4254_;
v___y_4234_ = v___y_4255_;
v___y_4235_ = v___y_4256_;
v_size_4236_ = v_size_4264_;
v_interpreted_4237_ = v_interpreted_4265_;
v_ctor_4238_ = v_ctor_4263_;
v___y_4239_ = v___y_4257_;
v___y_4240_ = v___y_4258_;
v___y_4241_ = v___y_4259_;
goto v___jp_4224_;
}
}
}
v___jp_4266_:
{
uint8_t v_interpreted_4281_; 
v_interpreted_4281_ = lean_ctor_get_uint8(v___y_4267_, sizeof(void*)*12 + 1);
if (v_interpreted_4281_ == 0)
{
uint8_t v_ctor_4282_; 
v_ctor_4282_ = lean_ctor_get_uint8(v___y_4267_, sizeof(void*)*12 + 2);
v___y_4245_ = v___y_4267_;
v_ctor_4246_ = v_ctor_4282_;
v___y_4247_ = v_valueInconsistency_4269_;
v___y_4248_ = v___y_4273_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v_trueEqFalse_4270_;
v___y_4251_ = v___y_4272_;
v___y_4252_ = v___y_4279_;
v___y_4253_ = v___y_4278_;
v___y_4254_ = v___y_4277_;
v___y_4255_ = v___y_4274_;
v___y_4256_ = v___y_4268_;
v___y_4257_ = v___y_4276_;
v___y_4258_ = v___y_4275_;
v___y_4259_ = v___y_4271_;
goto v___jp_4244_;
}
else
{
uint8_t v_interpreted_4283_; 
v_interpreted_4283_ = lean_ctor_get_uint8(v___y_4268_, sizeof(void*)*12 + 1);
if (v_interpreted_4283_ == 0)
{
v___y_4193_ = v_valueInconsistency_4269_;
v___y_4194_ = v___y_4267_;
v___y_4195_ = v___y_4273_;
v___y_4196_ = v___y_4280_;
v___y_4197_ = v_trueEqFalse_4270_;
v___y_4198_ = v___y_4272_;
v___y_4199_ = v___y_4279_;
v___y_4200_ = v___y_4278_;
v___y_4201_ = v___y_4277_;
v___y_4202_ = v___y_4274_;
v___y_4203_ = v___y_4268_;
v___y_4204_ = v___y_4276_;
v___y_4205_ = v___y_4275_;
v___y_4206_ = v___y_4271_;
goto v___jp_4192_;
}
else
{
uint8_t v_ctor_4284_; 
v_ctor_4284_ = lean_ctor_get_uint8(v___y_4267_, sizeof(void*)*12 + 2);
v___y_4245_ = v___y_4267_;
v_ctor_4246_ = v_ctor_4284_;
v___y_4247_ = v_valueInconsistency_4269_;
v___y_4248_ = v___y_4273_;
v___y_4249_ = v___y_4280_;
v___y_4250_ = v_trueEqFalse_4270_;
v___y_4251_ = v___y_4272_;
v___y_4252_ = v___y_4279_;
v___y_4253_ = v___y_4278_;
v___y_4254_ = v___y_4277_;
v___y_4255_ = v___y_4274_;
v___y_4256_ = v___y_4268_;
v___y_4257_ = v___y_4276_;
v___y_4258_ = v___y_4275_;
v___y_4259_ = v___y_4271_;
goto v___jp_4244_;
}
}
}
v___jp_4285_:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4296_, v___y_4292_, v___y_4289_, v___y_4294_, v___y_4286_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_dec_ref_known(v___x_4298_, 1);
v___y_4267_ = v___y_4287_;
v___y_4268_ = v___y_4295_;
v_valueInconsistency_4269_ = v___x_4076_;
v_trueEqFalse_4270_ = v___x_4081_;
v___y_4271_ = v___y_4296_;
v___y_4272_ = v___y_4291_;
v___y_4273_ = v___y_4290_;
v___y_4274_ = v___y_4288_;
v___y_4275_ = v___y_4293_;
v___y_4276_ = v___y_4297_;
v___y_4277_ = v___y_4292_;
v___y_4278_ = v___y_4289_;
v___y_4279_ = v___y_4294_;
v___y_4280_ = v___y_4286_;
goto v___jp_4266_;
}
else
{
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___y_4287_);
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
return v___x_4298_;
}
}
v___jp_4299_:
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_Meta_Grind_hasSameType(v___y_4303_, v___y_4309_, v___y_4307_, v___y_4304_, v___y_4310_, v___y_4301_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; uint8_t v___x_4316_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = lean_unbox(v_a_4315_);
lean_dec(v_a_4315_);
if (v___x_4316_ == 0)
{
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4311_;
v_valueInconsistency_4269_ = v___x_4076_;
v_trueEqFalse_4270_ = v___x_4076_;
v___y_4271_ = v___y_4312_;
v___y_4272_ = v___y_4306_;
v___y_4273_ = v___y_4305_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4308_;
v___y_4276_ = v___y_4313_;
v___y_4277_ = v___y_4307_;
v___y_4278_ = v___y_4304_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___y_4301_;
goto v___jp_4266_;
}
else
{
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4311_;
v_valueInconsistency_4269_ = v___x_4081_;
v_trueEqFalse_4270_ = v___x_4076_;
v___y_4271_ = v___y_4312_;
v___y_4272_ = v___y_4306_;
v___y_4273_ = v___y_4305_;
v___y_4274_ = v___y_4302_;
v___y_4275_ = v___y_4308_;
v___y_4276_ = v___y_4313_;
v___y_4277_ = v___y_4307_;
v___y_4278_ = v___y_4304_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___y_4301_;
goto v___jp_4266_;
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec_ref(v___y_4311_);
lean_dec_ref(v___y_4300_);
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4317_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4314_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4314_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
v___jp_4325_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_st_ref_get(v___y_4326_);
lean_inc_ref(v_root_4072_);
v___x_4337_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4336_, v_root_4072_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___x_4336_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4337_, 1);
v___x_4339_ = lean_st_ref_get(v___y_4326_);
lean_inc_ref(v_root_4073_);
v___x_4340_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4339_, v_root_4073_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___x_4339_);
if (lean_obj_tag(v___x_4340_) == 0)
{
uint8_t v_interpreted_4341_; 
v_interpreted_4341_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*12 + 1);
if (v_interpreted_4341_ == 0)
{
lean_object* v_a_4342_; uint8_t v_ctor_4343_; 
v_a_4342_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4340_, 1);
v_ctor_4343_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*12 + 2);
v___y_4245_ = v_a_4338_;
v_ctor_4246_ = v_ctor_4343_;
v___y_4247_ = v___x_4076_;
v___y_4248_ = v___y_4328_;
v___y_4249_ = v___y_4335_;
v___y_4250_ = v___x_4076_;
v___y_4251_ = v___y_4327_;
v___y_4252_ = v___y_4334_;
v___y_4253_ = v___y_4333_;
v___y_4254_ = v___y_4332_;
v___y_4255_ = v___y_4329_;
v___y_4256_ = v_a_4342_;
v___y_4257_ = v___y_4331_;
v___y_4258_ = v___y_4330_;
v___y_4259_ = v___y_4326_;
goto v___jp_4244_;
}
else
{
lean_object* v_a_4344_; uint8_t v_interpreted_4345_; 
v_a_4344_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4340_, 1);
v_interpreted_4345_ = lean_ctor_get_uint8(v_a_4344_, sizeof(void*)*12 + 1);
if (v_interpreted_4345_ == 0)
{
v___y_4193_ = v___x_4076_;
v___y_4194_ = v_a_4338_;
v___y_4195_ = v___y_4328_;
v___y_4196_ = v___y_4335_;
v___y_4197_ = v___x_4076_;
v___y_4198_ = v___y_4327_;
v___y_4199_ = v___y_4334_;
v___y_4200_ = v___y_4333_;
v___y_4201_ = v___y_4332_;
v___y_4202_ = v___y_4329_;
v___y_4203_ = v_a_4344_;
v___y_4204_ = v___y_4331_;
v___y_4205_ = v___y_4330_;
v___y_4206_ = v___y_4326_;
goto v___jp_4192_;
}
else
{
lean_object* v_self_4346_; uint8_t v_ctor_4347_; uint8_t v_heqProofs_4348_; lean_object* v_self_4349_; uint8_t v_heqProofs_4350_; uint8_t v___x_4351_; 
v_self_4346_ = lean_ctor_get(v_a_4338_, 0);
v_ctor_4347_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*12 + 2);
v_heqProofs_4348_ = lean_ctor_get_uint8(v_a_4338_, sizeof(void*)*12 + 4);
v_self_4349_ = lean_ctor_get(v_a_4344_, 0);
v_heqProofs_4350_ = lean_ctor_get_uint8(v_a_4344_, sizeof(void*)*12 + 4);
v___x_4351_ = l_Lean_Expr_isTrue(v_root_4072_);
if (v___x_4351_ == 0)
{
uint8_t v___x_4352_; 
v___x_4352_ = l_Lean_Expr_isTrue(v_root_4073_);
if (v___x_4352_ == 0)
{
if (v_isHEq_4051_ == 0)
{
if (v_heqProofs_4348_ == 0)
{
if (v_heqProofs_4350_ == 0)
{
v___y_4245_ = v_a_4338_;
v_ctor_4246_ = v_ctor_4347_;
v___y_4247_ = v___x_4081_;
v___y_4248_ = v___y_4328_;
v___y_4249_ = v___y_4335_;
v___y_4250_ = v___x_4076_;
v___y_4251_ = v___y_4327_;
v___y_4252_ = v___y_4334_;
v___y_4253_ = v___y_4333_;
v___y_4254_ = v___y_4332_;
v___y_4255_ = v___y_4329_;
v___y_4256_ = v_a_4344_;
v___y_4257_ = v___y_4331_;
v___y_4258_ = v___y_4330_;
v___y_4259_ = v___y_4326_;
goto v___jp_4244_;
}
else
{
lean_inc_ref(v_self_4349_);
lean_inc_ref(v_self_4346_);
v___y_4300_ = v_a_4338_;
v___y_4301_ = v___y_4335_;
v___y_4302_ = v___y_4329_;
v___y_4303_ = v_self_4346_;
v___y_4304_ = v___y_4333_;
v___y_4305_ = v___y_4328_;
v___y_4306_ = v___y_4327_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4330_;
v___y_4309_ = v_self_4349_;
v___y_4310_ = v___y_4334_;
v___y_4311_ = v_a_4344_;
v___y_4312_ = v___y_4326_;
v___y_4313_ = v___y_4331_;
goto v___jp_4299_;
}
}
else
{
lean_inc_ref(v_self_4349_);
lean_inc_ref(v_self_4346_);
v___y_4300_ = v_a_4338_;
v___y_4301_ = v___y_4335_;
v___y_4302_ = v___y_4329_;
v___y_4303_ = v_self_4346_;
v___y_4304_ = v___y_4333_;
v___y_4305_ = v___y_4328_;
v___y_4306_ = v___y_4327_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4330_;
v___y_4309_ = v_self_4349_;
v___y_4310_ = v___y_4334_;
v___y_4311_ = v_a_4344_;
v___y_4312_ = v___y_4326_;
v___y_4313_ = v___y_4331_;
goto v___jp_4299_;
}
}
else
{
lean_inc_ref(v_self_4349_);
lean_inc_ref(v_self_4346_);
v___y_4300_ = v_a_4338_;
v___y_4301_ = v___y_4335_;
v___y_4302_ = v___y_4329_;
v___y_4303_ = v_self_4346_;
v___y_4304_ = v___y_4333_;
v___y_4305_ = v___y_4328_;
v___y_4306_ = v___y_4327_;
v___y_4307_ = v___y_4332_;
v___y_4308_ = v___y_4330_;
v___y_4309_ = v_self_4349_;
v___y_4310_ = v___y_4334_;
v___y_4311_ = v_a_4344_;
v___y_4312_ = v___y_4326_;
v___y_4313_ = v___y_4331_;
goto v___jp_4299_;
}
}
else
{
v___y_4286_ = v___y_4335_;
v___y_4287_ = v_a_4338_;
v___y_4288_ = v___y_4329_;
v___y_4289_ = v___y_4333_;
v___y_4290_ = v___y_4328_;
v___y_4291_ = v___y_4327_;
v___y_4292_ = v___y_4332_;
v___y_4293_ = v___y_4330_;
v___y_4294_ = v___y_4334_;
v___y_4295_ = v_a_4344_;
v___y_4296_ = v___y_4326_;
v___y_4297_ = v___y_4331_;
goto v___jp_4285_;
}
}
else
{
v___y_4286_ = v___y_4335_;
v___y_4287_ = v_a_4338_;
v___y_4288_ = v___y_4329_;
v___y_4289_ = v___y_4333_;
v___y_4290_ = v___y_4328_;
v___y_4291_ = v___y_4327_;
v___y_4292_ = v___y_4332_;
v___y_4293_ = v___y_4330_;
v___y_4294_ = v___y_4334_;
v___y_4295_ = v_a_4344_;
v___y_4296_ = v___y_4326_;
v___y_4297_ = v___y_4331_;
goto v___jp_4285_;
}
}
}
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_dec(v_a_4338_);
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4353_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4340_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4340_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4361_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4337_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4337_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
else
{
lean_object* v_toCold_4407_; lean_object* v_options_4408_; uint8_t v_hasTrace_4409_; 
lean_dec(v_a_4071_);
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
v_toCold_4407_ = lean_ctor_get(v_a_4060_, 0);
v_options_4408_ = lean_ctor_get(v_toCold_4407_, 2);
v_hasTrace_4409_ = lean_ctor_get_uint8(v_options_4408_, sizeof(void*)*1);
if (v_hasTrace_4409_ == 0)
{
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
goto v___jp_4063_;
}
else
{
lean_object* v_inheritedTraceOptions_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; 
v_inheritedTraceOptions_4410_ = lean_ctor_get(v_toCold_4407_, 11);
v___x_4411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4413_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4410_, v_options_4408_, v___x_4412_);
if (v___x_4413_ == 0)
{
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
goto v___jp_4063_;
}
else
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Meta_Grind_updateLastTag(v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4415_; 
lean_dec_ref_known(v___x_4414_, 1);
v___x_4415_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4048_, v_a_4052_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4049_, v_a_4052_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_a_4416_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
lean_ctor_set(v___x_4421_, 1, v_a_4418_);
v___x_4422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4411_, v___x_4423_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_dec_ref_known(v___x_4424_, 1);
goto v___jp_4063_;
}
else
{
return v___x_4424_;
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4416_);
v_a_4425_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4417_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4417_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec_ref(v_rhs_4049_);
v_a_4433_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4415_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4415_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
return v___x_4414_;
}
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_a_4068_);
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4441_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4070_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4070_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec_ref(v_proof_4050_);
lean_dec_ref(v_rhs_4049_);
lean_dec_ref(v_lhs_4048_);
v_a_4449_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4067_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4067_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
v___jp_4063_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_box(0);
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4457_, lean_object* v_rhs_4458_, lean_object* v_proof_4459_, lean_object* v_isHEq_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
uint8_t v_isHEq_boxed_4472_; lean_object* v_res_4473_; 
v_isHEq_boxed_4472_ = lean_unbox(v_isHEq_4460_);
v_res_4473_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4457_, v_rhs_4458_, v_proof_4459_, v_isHEq_boxed_4472_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec(v_a_4461_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v_toGoalState_4479_; lean_object* v_mvarId_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4521_; 
v___x_4478_ = lean_st_ref_take(v_a_4476_);
v_toGoalState_4479_ = lean_ctor_get(v___x_4478_, 0);
v_mvarId_4480_ = lean_ctor_get(v___x_4478_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4482_ = v___x_4478_;
v_isShared_4483_ = v_isSharedCheck_4521_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_mvarId_4480_);
lean_inc(v_toGoalState_4479_);
lean_dec(v___x_4478_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4521_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v_nextDeclIdx_4484_; lean_object* v_enodeMap_4485_; lean_object* v_exprs_4486_; lean_object* v_parents_4487_; lean_object* v_congrTable_4488_; lean_object* v_appMap_4489_; lean_object* v_indicesFound_4490_; lean_object* v_internalizing_4491_; uint8_t v_inconsistent_4492_; lean_object* v_nextIdx_4493_; lean_object* v_newRawFacts_4494_; lean_object* v_facts_4495_; lean_object* v_extThms_4496_; lean_object* v_ematch_4497_; lean_object* v_inj_4498_; lean_object* v_split_4499_; lean_object* v_clean_4500_; lean_object* v_sstates_4501_; lean_object* v_goalStack_4502_; uint64_t v_introBase_4503_; lean_object* v_numIntros_4504_; lean_object* v_relevance_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4519_; 
v_nextDeclIdx_4484_ = lean_ctor_get(v_toGoalState_4479_, 0);
v_enodeMap_4485_ = lean_ctor_get(v_toGoalState_4479_, 1);
v_exprs_4486_ = lean_ctor_get(v_toGoalState_4479_, 2);
v_parents_4487_ = lean_ctor_get(v_toGoalState_4479_, 3);
v_congrTable_4488_ = lean_ctor_get(v_toGoalState_4479_, 4);
v_appMap_4489_ = lean_ctor_get(v_toGoalState_4479_, 5);
v_indicesFound_4490_ = lean_ctor_get(v_toGoalState_4479_, 6);
v_internalizing_4491_ = lean_ctor_get(v_toGoalState_4479_, 8);
v_inconsistent_4492_ = lean_ctor_get_uint8(v_toGoalState_4479_, sizeof(void*)*21 + 8);
v_nextIdx_4493_ = lean_ctor_get(v_toGoalState_4479_, 9);
v_newRawFacts_4494_ = lean_ctor_get(v_toGoalState_4479_, 10);
v_facts_4495_ = lean_ctor_get(v_toGoalState_4479_, 11);
v_extThms_4496_ = lean_ctor_get(v_toGoalState_4479_, 12);
v_ematch_4497_ = lean_ctor_get(v_toGoalState_4479_, 13);
v_inj_4498_ = lean_ctor_get(v_toGoalState_4479_, 14);
v_split_4499_ = lean_ctor_get(v_toGoalState_4479_, 15);
v_clean_4500_ = lean_ctor_get(v_toGoalState_4479_, 16);
v_sstates_4501_ = lean_ctor_get(v_toGoalState_4479_, 17);
v_goalStack_4502_ = lean_ctor_get(v_toGoalState_4479_, 18);
v_introBase_4503_ = lean_ctor_get_uint64(v_toGoalState_4479_, sizeof(void*)*21);
v_numIntros_4504_ = lean_ctor_get(v_toGoalState_4479_, 19);
v_relevance_4505_ = lean_ctor_get(v_toGoalState_4479_, 20);
v_isSharedCheck_4519_ = !lean_is_exclusive(v_toGoalState_4479_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v_toGoalState_4479_, 7);
lean_dec(v_unused_4520_);
v___x_4507_ = v_toGoalState_4479_;
v_isShared_4508_ = v_isSharedCheck_4519_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_relevance_4505_);
lean_inc(v_numIntros_4504_);
lean_inc(v_goalStack_4502_);
lean_inc(v_sstates_4501_);
lean_inc(v_clean_4500_);
lean_inc(v_split_4499_);
lean_inc(v_inj_4498_);
lean_inc(v_ematch_4497_);
lean_inc(v_extThms_4496_);
lean_inc(v_facts_4495_);
lean_inc(v_newRawFacts_4494_);
lean_inc(v_nextIdx_4493_);
lean_inc(v_internalizing_4491_);
lean_inc(v_indicesFound_4490_);
lean_inc(v_appMap_4489_);
lean_inc(v_congrTable_4488_);
lean_inc(v_parents_4487_);
lean_inc(v_exprs_4486_);
lean_inc(v_enodeMap_4485_);
lean_inc(v_nextDeclIdx_4484_);
lean_dec(v_toGoalState_4479_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4519_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4509_ = lean_box(0);
v___x_4510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4508_ == 0)
{
lean_ctor_set(v___x_4507_, 7, v___x_4510_);
v___x_4512_ = v___x_4507_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_nextDeclIdx_4484_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_enodeMap_4485_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_exprs_4486_);
lean_ctor_set(v_reuseFailAlloc_4518_, 3, v_parents_4487_);
lean_ctor_set(v_reuseFailAlloc_4518_, 4, v_congrTable_4488_);
lean_ctor_set(v_reuseFailAlloc_4518_, 5, v_appMap_4489_);
lean_ctor_set(v_reuseFailAlloc_4518_, 6, v_indicesFound_4490_);
lean_ctor_set(v_reuseFailAlloc_4518_, 7, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4518_, 8, v_internalizing_4491_);
lean_ctor_set(v_reuseFailAlloc_4518_, 9, v_nextIdx_4493_);
lean_ctor_set(v_reuseFailAlloc_4518_, 10, v_newRawFacts_4494_);
lean_ctor_set(v_reuseFailAlloc_4518_, 11, v_facts_4495_);
lean_ctor_set(v_reuseFailAlloc_4518_, 12, v_extThms_4496_);
lean_ctor_set(v_reuseFailAlloc_4518_, 13, v_ematch_4497_);
lean_ctor_set(v_reuseFailAlloc_4518_, 14, v_inj_4498_);
lean_ctor_set(v_reuseFailAlloc_4518_, 15, v_split_4499_);
lean_ctor_set(v_reuseFailAlloc_4518_, 16, v_clean_4500_);
lean_ctor_set(v_reuseFailAlloc_4518_, 17, v_sstates_4501_);
lean_ctor_set(v_reuseFailAlloc_4518_, 18, v_goalStack_4502_);
lean_ctor_set(v_reuseFailAlloc_4518_, 19, v_numIntros_4504_);
lean_ctor_set(v_reuseFailAlloc_4518_, 20, v_relevance_4505_);
lean_ctor_set_uint8(v_reuseFailAlloc_4518_, sizeof(void*)*21 + 8, v_inconsistent_4492_);
lean_ctor_set_uint64(v_reuseFailAlloc_4518_, sizeof(void*)*21, v_introBase_4503_);
v___x_4512_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4514_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4512_);
v___x_4514_ = v___x_4482_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4517_, 1, v_mvarId_4480_);
v___x_4514_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_st_ref_put(v_a_4476_, v___x_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4509_);
return v___x_4516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4522_);
lean_dec(v_a_4522_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4525_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec(v_a_4537_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4549_){
_start:
{
lean_object* v___x_4551_; lean_object* v_toGoalState_4552_; lean_object* v_toProcess_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
v___x_4551_ = lean_st_ref_get(v_a_4549_);
v_toGoalState_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc_ref(v_toGoalState_4552_);
lean_dec(v___x_4551_);
v_toProcess_4553_ = lean_ctor_get(v_toGoalState_4552_, 7);
lean_inc_ref(v_toProcess_4553_);
lean_dec_ref(v_toGoalState_4552_);
v___x_4554_ = lean_array_get_size(v_toProcess_4553_);
v___x_4555_ = lean_unsigned_to_nat(1u);
v___x_4556_ = lean_nat_sub(v___x_4554_, v___x_4555_);
v___x_4557_ = lean_nat_dec_lt(v___x_4556_, v___x_4554_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4558_; lean_object* v___x_4559_; 
lean_dec(v___x_4556_);
lean_dec_ref(v_toProcess_4553_);
v___x_4558_ = lean_box(0);
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v_toGoalState_4563_; lean_object* v_mvarId_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4604_; 
v___x_4560_ = lean_array_fget(v_toProcess_4553_, v___x_4556_);
lean_dec(v___x_4556_);
lean_dec_ref(v_toProcess_4553_);
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
v___x_4562_ = lean_st_ref_take(v_a_4549_);
v_toGoalState_4563_ = lean_ctor_get(v___x_4562_, 0);
v_mvarId_4564_ = lean_ctor_get(v___x_4562_, 1);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4566_ = v___x_4562_;
v_isShared_4567_ = v_isSharedCheck_4604_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_mvarId_4564_);
lean_inc(v_toGoalState_4563_);
lean_dec(v___x_4562_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4604_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v_nextDeclIdx_4568_; lean_object* v_enodeMap_4569_; lean_object* v_exprs_4570_; lean_object* v_parents_4571_; lean_object* v_congrTable_4572_; lean_object* v_appMap_4573_; lean_object* v_indicesFound_4574_; lean_object* v_toProcess_4575_; lean_object* v_internalizing_4576_; uint8_t v_inconsistent_4577_; lean_object* v_nextIdx_4578_; lean_object* v_newRawFacts_4579_; lean_object* v_facts_4580_; lean_object* v_extThms_4581_; lean_object* v_ematch_4582_; lean_object* v_inj_4583_; lean_object* v_split_4584_; lean_object* v_clean_4585_; lean_object* v_sstates_4586_; lean_object* v_goalStack_4587_; uint64_t v_introBase_4588_; lean_object* v_numIntros_4589_; lean_object* v_relevance_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4603_; 
v_nextDeclIdx_4568_ = lean_ctor_get(v_toGoalState_4563_, 0);
v_enodeMap_4569_ = lean_ctor_get(v_toGoalState_4563_, 1);
v_exprs_4570_ = lean_ctor_get(v_toGoalState_4563_, 2);
v_parents_4571_ = lean_ctor_get(v_toGoalState_4563_, 3);
v_congrTable_4572_ = lean_ctor_get(v_toGoalState_4563_, 4);
v_appMap_4573_ = lean_ctor_get(v_toGoalState_4563_, 5);
v_indicesFound_4574_ = lean_ctor_get(v_toGoalState_4563_, 6);
v_toProcess_4575_ = lean_ctor_get(v_toGoalState_4563_, 7);
v_internalizing_4576_ = lean_ctor_get(v_toGoalState_4563_, 8);
v_inconsistent_4577_ = lean_ctor_get_uint8(v_toGoalState_4563_, sizeof(void*)*21 + 8);
v_nextIdx_4578_ = lean_ctor_get(v_toGoalState_4563_, 9);
v_newRawFacts_4579_ = lean_ctor_get(v_toGoalState_4563_, 10);
v_facts_4580_ = lean_ctor_get(v_toGoalState_4563_, 11);
v_extThms_4581_ = lean_ctor_get(v_toGoalState_4563_, 12);
v_ematch_4582_ = lean_ctor_get(v_toGoalState_4563_, 13);
v_inj_4583_ = lean_ctor_get(v_toGoalState_4563_, 14);
v_split_4584_ = lean_ctor_get(v_toGoalState_4563_, 15);
v_clean_4585_ = lean_ctor_get(v_toGoalState_4563_, 16);
v_sstates_4586_ = lean_ctor_get(v_toGoalState_4563_, 17);
v_goalStack_4587_ = lean_ctor_get(v_toGoalState_4563_, 18);
v_introBase_4588_ = lean_ctor_get_uint64(v_toGoalState_4563_, sizeof(void*)*21);
v_numIntros_4589_ = lean_ctor_get(v_toGoalState_4563_, 19);
v_relevance_4590_ = lean_ctor_get(v_toGoalState_4563_, 20);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_toGoalState_4563_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4592_ = v_toGoalState_4563_;
v_isShared_4593_ = v_isSharedCheck_4603_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_relevance_4590_);
lean_inc(v_numIntros_4589_);
lean_inc(v_goalStack_4587_);
lean_inc(v_sstates_4586_);
lean_inc(v_clean_4585_);
lean_inc(v_split_4584_);
lean_inc(v_inj_4583_);
lean_inc(v_ematch_4582_);
lean_inc(v_extThms_4581_);
lean_inc(v_facts_4580_);
lean_inc(v_newRawFacts_4579_);
lean_inc(v_nextIdx_4578_);
lean_inc(v_internalizing_4576_);
lean_inc(v_toProcess_4575_);
lean_inc(v_indicesFound_4574_);
lean_inc(v_appMap_4573_);
lean_inc(v_congrTable_4572_);
lean_inc(v_parents_4571_);
lean_inc(v_exprs_4570_);
lean_inc(v_enodeMap_4569_);
lean_inc(v_nextDeclIdx_4568_);
lean_dec(v_toGoalState_4563_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4603_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
v___x_4594_ = lean_array_pop(v_toProcess_4575_);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 7, v___x_4594_);
v___x_4596_ = v___x_4592_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_nextDeclIdx_4568_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_enodeMap_4569_);
lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_exprs_4570_);
lean_ctor_set(v_reuseFailAlloc_4602_, 3, v_parents_4571_);
lean_ctor_set(v_reuseFailAlloc_4602_, 4, v_congrTable_4572_);
lean_ctor_set(v_reuseFailAlloc_4602_, 5, v_appMap_4573_);
lean_ctor_set(v_reuseFailAlloc_4602_, 6, v_indicesFound_4574_);
lean_ctor_set(v_reuseFailAlloc_4602_, 7, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4602_, 8, v_internalizing_4576_);
lean_ctor_set(v_reuseFailAlloc_4602_, 9, v_nextIdx_4578_);
lean_ctor_set(v_reuseFailAlloc_4602_, 10, v_newRawFacts_4579_);
lean_ctor_set(v_reuseFailAlloc_4602_, 11, v_facts_4580_);
lean_ctor_set(v_reuseFailAlloc_4602_, 12, v_extThms_4581_);
lean_ctor_set(v_reuseFailAlloc_4602_, 13, v_ematch_4582_);
lean_ctor_set(v_reuseFailAlloc_4602_, 14, v_inj_4583_);
lean_ctor_set(v_reuseFailAlloc_4602_, 15, v_split_4584_);
lean_ctor_set(v_reuseFailAlloc_4602_, 16, v_clean_4585_);
lean_ctor_set(v_reuseFailAlloc_4602_, 17, v_sstates_4586_);
lean_ctor_set(v_reuseFailAlloc_4602_, 18, v_goalStack_4587_);
lean_ctor_set(v_reuseFailAlloc_4602_, 19, v_numIntros_4589_);
lean_ctor_set(v_reuseFailAlloc_4602_, 20, v_relevance_4590_);
lean_ctor_set_uint8(v_reuseFailAlloc_4602_, sizeof(void*)*21 + 8, v_inconsistent_4577_);
lean_ctor_set_uint64(v_reuseFailAlloc_4602_, sizeof(void*)*21, v_introBase_4588_);
v___x_4596_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4598_; 
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4596_);
v___x_4598_ = v___x_4566_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4596_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_mvarId_4564_);
v___x_4598_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_st_ref_put(v_a_4549_, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4561_);
return v___x_4600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4605_);
lean_dec(v_a_4605_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4608_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec(v_a_4620_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4632_, lean_object* v_rhs_4633_, lean_object* v_proof_4634_, uint8_t v_isHEq_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4632_, v_rhs_4633_, v_proof_4634_, v_isHEq_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v___x_4648_; 
lean_dec_ref_known(v___x_4647_, 1);
lean_inc(v_a_4645_);
lean_inc_ref(v_a_4644_);
lean_inc(v_a_4643_);
lean_inc_ref(v_a_4642_);
lean_inc(v_a_4641_);
lean_inc_ref(v_a_4640_);
lean_inc(v_a_4639_);
lean_inc_ref(v_a_4638_);
lean_inc(v_a_4637_);
lean_inc(v_a_4636_);
v___x_4648_ = lean_grind_process_to_do(v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
return v___x_4648_;
}
else
{
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4649_, lean_object* v_rhs_4650_, lean_object* v_proof_4651_, lean_object* v_isHEq_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
uint8_t v_isHEq_boxed_4664_; lean_object* v_res_4665_; 
v_isHEq_boxed_4664_ = lean_unbox(v_isHEq_4652_);
v_res_4665_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4649_, v_rhs_4650_, v_proof_4651_, v_isHEq_boxed_4664_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec(v_a_4653_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4666_, lean_object* v_rhs_4667_, lean_object* v_proof_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
uint8_t v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = 0;
v___x_4681_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4666_, v_rhs_4667_, v_proof_4668_, v___x_4680_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4682_, lean_object* v_rhs_4683_, lean_object* v_proof_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4682_, v_rhs_4683_, v_proof_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4697_, lean_object* v_rhs_4698_, lean_object* v_proof_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_){
_start:
{
uint8_t v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = 1;
v___x_4712_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4697_, v_rhs_4698_, v_proof_4699_, v___x_4711_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4713_, lean_object* v_rhs_4714_, lean_object* v_proof_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4713_, v_rhs_4714_, v_proof_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
lean_dec(v_a_4721_);
lean_dec_ref(v_a_4720_);
lean_dec(v_a_4719_);
lean_dec_ref(v_a_4718_);
lean_dec(v_a_4717_);
lean_dec(v_a_4716_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v___x_4731_; lean_object* v_toGoalState_4732_; lean_object* v_mvarId_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4774_; 
v___x_4731_ = lean_st_ref_take(v_a_4729_);
v_toGoalState_4732_ = lean_ctor_get(v___x_4731_, 0);
v_mvarId_4733_ = lean_ctor_get(v___x_4731_, 1);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4735_ = v___x_4731_;
v_isShared_4736_ = v_isSharedCheck_4774_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_mvarId_4733_);
lean_inc(v_toGoalState_4732_);
lean_dec(v___x_4731_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4774_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_nextDeclIdx_4737_; lean_object* v_enodeMap_4738_; lean_object* v_exprs_4739_; lean_object* v_parents_4740_; lean_object* v_congrTable_4741_; lean_object* v_appMap_4742_; lean_object* v_indicesFound_4743_; lean_object* v_toProcess_4744_; lean_object* v_internalizing_4745_; uint8_t v_inconsistent_4746_; lean_object* v_nextIdx_4747_; lean_object* v_newRawFacts_4748_; lean_object* v_facts_4749_; lean_object* v_extThms_4750_; lean_object* v_ematch_4751_; lean_object* v_inj_4752_; lean_object* v_split_4753_; lean_object* v_clean_4754_; lean_object* v_sstates_4755_; lean_object* v_goalStack_4756_; uint64_t v_introBase_4757_; lean_object* v_numIntros_4758_; lean_object* v_relevance_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4773_; 
v_nextDeclIdx_4737_ = lean_ctor_get(v_toGoalState_4732_, 0);
v_enodeMap_4738_ = lean_ctor_get(v_toGoalState_4732_, 1);
v_exprs_4739_ = lean_ctor_get(v_toGoalState_4732_, 2);
v_parents_4740_ = lean_ctor_get(v_toGoalState_4732_, 3);
v_congrTable_4741_ = lean_ctor_get(v_toGoalState_4732_, 4);
v_appMap_4742_ = lean_ctor_get(v_toGoalState_4732_, 5);
v_indicesFound_4743_ = lean_ctor_get(v_toGoalState_4732_, 6);
v_toProcess_4744_ = lean_ctor_get(v_toGoalState_4732_, 7);
v_internalizing_4745_ = lean_ctor_get(v_toGoalState_4732_, 8);
v_inconsistent_4746_ = lean_ctor_get_uint8(v_toGoalState_4732_, sizeof(void*)*21 + 8);
v_nextIdx_4747_ = lean_ctor_get(v_toGoalState_4732_, 9);
v_newRawFacts_4748_ = lean_ctor_get(v_toGoalState_4732_, 10);
v_facts_4749_ = lean_ctor_get(v_toGoalState_4732_, 11);
v_extThms_4750_ = lean_ctor_get(v_toGoalState_4732_, 12);
v_ematch_4751_ = lean_ctor_get(v_toGoalState_4732_, 13);
v_inj_4752_ = lean_ctor_get(v_toGoalState_4732_, 14);
v_split_4753_ = lean_ctor_get(v_toGoalState_4732_, 15);
v_clean_4754_ = lean_ctor_get(v_toGoalState_4732_, 16);
v_sstates_4755_ = lean_ctor_get(v_toGoalState_4732_, 17);
v_goalStack_4756_ = lean_ctor_get(v_toGoalState_4732_, 18);
v_introBase_4757_ = lean_ctor_get_uint64(v_toGoalState_4732_, sizeof(void*)*21);
v_numIntros_4758_ = lean_ctor_get(v_toGoalState_4732_, 19);
v_relevance_4759_ = lean_ctor_get(v_toGoalState_4732_, 20);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_toGoalState_4732_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4761_ = v_toGoalState_4732_;
v_isShared_4762_ = v_isSharedCheck_4773_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_relevance_4759_);
lean_inc(v_numIntros_4758_);
lean_inc(v_goalStack_4756_);
lean_inc(v_sstates_4755_);
lean_inc(v_clean_4754_);
lean_inc(v_split_4753_);
lean_inc(v_inj_4752_);
lean_inc(v_ematch_4751_);
lean_inc(v_extThms_4750_);
lean_inc(v_facts_4749_);
lean_inc(v_newRawFacts_4748_);
lean_inc(v_nextIdx_4747_);
lean_inc(v_internalizing_4745_);
lean_inc(v_toProcess_4744_);
lean_inc(v_indicesFound_4743_);
lean_inc(v_appMap_4742_);
lean_inc(v_congrTable_4741_);
lean_inc(v_parents_4740_);
lean_inc(v_exprs_4739_);
lean_inc(v_enodeMap_4738_);
lean_inc(v_nextDeclIdx_4737_);
lean_dec(v_toGoalState_4732_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4773_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4763_ = lean_box(0);
v___x_4764_ = l_Lean_PersistentArray_push___redArg(v_facts_4749_, v_fact_4728_);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 11, v___x_4764_);
v___x_4766_ = v___x_4761_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 21, 9);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_nextDeclIdx_4737_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_enodeMap_4738_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_exprs_4739_);
lean_ctor_set(v_reuseFailAlloc_4772_, 3, v_parents_4740_);
lean_ctor_set(v_reuseFailAlloc_4772_, 4, v_congrTable_4741_);
lean_ctor_set(v_reuseFailAlloc_4772_, 5, v_appMap_4742_);
lean_ctor_set(v_reuseFailAlloc_4772_, 6, v_indicesFound_4743_);
lean_ctor_set(v_reuseFailAlloc_4772_, 7, v_toProcess_4744_);
lean_ctor_set(v_reuseFailAlloc_4772_, 8, v_internalizing_4745_);
lean_ctor_set(v_reuseFailAlloc_4772_, 9, v_nextIdx_4747_);
lean_ctor_set(v_reuseFailAlloc_4772_, 10, v_newRawFacts_4748_);
lean_ctor_set(v_reuseFailAlloc_4772_, 11, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4772_, 12, v_extThms_4750_);
lean_ctor_set(v_reuseFailAlloc_4772_, 13, v_ematch_4751_);
lean_ctor_set(v_reuseFailAlloc_4772_, 14, v_inj_4752_);
lean_ctor_set(v_reuseFailAlloc_4772_, 15, v_split_4753_);
lean_ctor_set(v_reuseFailAlloc_4772_, 16, v_clean_4754_);
lean_ctor_set(v_reuseFailAlloc_4772_, 17, v_sstates_4755_);
lean_ctor_set(v_reuseFailAlloc_4772_, 18, v_goalStack_4756_);
lean_ctor_set(v_reuseFailAlloc_4772_, 19, v_numIntros_4758_);
lean_ctor_set(v_reuseFailAlloc_4772_, 20, v_relevance_4759_);
lean_ctor_set_uint8(v_reuseFailAlloc_4772_, sizeof(void*)*21 + 8, v_inconsistent_4746_);
lean_ctor_set_uint64(v_reuseFailAlloc_4772_, sizeof(void*)*21, v_introBase_4757_);
v___x_4766_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4768_; 
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4766_);
v___x_4768_ = v___x_4735_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4766_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v_mvarId_4733_);
v___x_4768_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
v___x_4769_ = lean_st_ref_put(v_a_4729_, v___x_4768_);
v___x_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4763_);
return v___x_4770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4775_, v_a_4776_);
lean_dec(v_a_4776_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v___x_4791_; 
v___x_4791_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4779_, v_a_4780_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec(v_a_4793_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4805_, lean_object* v_rhs_4806_, lean_object* v_proof_4807_, lean_object* v_generation_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v___x_4820_; 
lean_inc_ref(v_rhs_4806_);
lean_inc_ref(v_lhs_4805_);
v___x_4820_ = l_Lean_Meta_mkEq(v_lhs_4805_, v_rhs_4806_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4832_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc_n(v_a_4821_, 2);
lean_dec_ref_known(v___x_4820_, 1);
v___x_4822_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4821_, v_a_4809_);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4832_ == 0)
{
lean_object* v_unused_4833_; 
v_unused_4833_ = lean_ctor_get(v___x_4822_, 0);
lean_dec(v_unused_4833_);
v___x_4824_ = v___x_4822_;
v_isShared_4825_ = v_isSharedCheck_4832_;
goto v_resetjp_4823_;
}
else
{
lean_dec(v___x_4822_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4832_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
lean_ctor_set_tag(v___x_4824_, 1);
lean_ctor_set(v___x_4824_, 0, v_a_4821_);
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4821_);
v___x_4827_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4828_; 
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc(v_a_4809_);
lean_inc_ref(v___x_4827_);
lean_inc(v_generation_4808_);
lean_inc_ref(v_lhs_4805_);
v___x_4828_ = lean_grind_internalize(v_lhs_4805_, v_generation_4808_, v___x_4827_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v___x_4829_; 
lean_dec_ref_known(v___x_4828_, 1);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc(v_a_4809_);
lean_inc_ref(v_rhs_4806_);
v___x_4829_ = lean_grind_internalize(v_rhs_4806_, v_generation_4808_, v___x_4827_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v___x_4830_; 
lean_dec_ref_known(v___x_4829_, 1);
v___x_4830_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4805_, v_rhs_4806_, v_proof_4807_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
return v___x_4830_;
}
else
{
lean_dec_ref(v_proof_4807_);
lean_dec_ref(v_rhs_4806_);
lean_dec_ref(v_lhs_4805_);
return v___x_4829_;
}
}
else
{
lean_dec_ref(v___x_4827_);
lean_dec(v_generation_4808_);
lean_dec_ref(v_proof_4807_);
lean_dec_ref(v_rhs_4806_);
lean_dec_ref(v_lhs_4805_);
return v___x_4828_;
}
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
lean_dec(v_generation_4808_);
lean_dec_ref(v_proof_4807_);
lean_dec_ref(v_rhs_4806_);
lean_dec_ref(v_lhs_4805_);
v_a_4834_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4820_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4820_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4842_, lean_object* v_rhs_4843_, lean_object* v_proof_4844_, lean_object* v_generation_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4842_, v_rhs_4843_, v_proof_4844_, v_generation_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec(v_a_4846_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4858_, lean_object* v_generation_4859_, lean_object* v_p_4860_, uint8_t v_isNeg_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_box(0);
lean_inc(v_a_4871_);
lean_inc_ref(v_a_4870_);
lean_inc(v_a_4869_);
lean_inc_ref(v_a_4868_);
lean_inc(v_a_4867_);
lean_inc_ref(v_a_4866_);
lean_inc(v_a_4865_);
lean_inc_ref(v_a_4864_);
lean_inc(v_a_4863_);
lean_inc(v_a_4862_);
lean_inc_ref(v_p_4860_);
v___x_4874_ = lean_grind_internalize(v_p_4860_, v_generation_4859_, v___x_4873_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_dec_ref_known(v___x_4874_, 1);
if (v_isNeg_4861_ == 0)
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4866_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4877_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
v___x_4877_ = l_Lean_Meta_mkEqTrue(v_proof_4858_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4879_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v___x_4879_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4860_, v_a_4876_, v_a_4878_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
return v___x_4879_;
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
lean_dec(v_a_4876_);
lean_dec_ref(v_p_4860_);
v_a_4880_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4877_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4877_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_dec_ref(v_p_4860_);
lean_dec_ref(v_proof_4858_);
v_a_4888_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4875_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4875_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
else
{
lean_object* v___x_4896_; 
v___x_4896_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4866_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4898_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4896_, 1);
v___x_4898_ = l_Lean_Meta_mkEqFalse(v_proof_4858_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4900_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref_known(v___x_4898_, 1);
v___x_4900_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4860_, v_a_4897_, v_a_4899_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
return v___x_4900_;
}
else
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
lean_dec(v_a_4897_);
lean_dec_ref(v_p_4860_);
v_a_4901_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4898_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4898_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
}
else
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
lean_dec_ref(v_p_4860_);
lean_dec_ref(v_proof_4858_);
v_a_4909_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4896_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4896_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4860_);
lean_dec_ref(v_proof_4858_);
return v___x_4874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4917_, lean_object* v_generation_4918_, lean_object* v_p_4919_, lean_object* v_isNeg_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
uint8_t v_isNeg_boxed_4932_; lean_object* v_res_4933_; 
v_isNeg_boxed_4932_ = lean_unbox(v_isNeg_4920_);
v_res_4933_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4917_, v_generation_4918_, v_p_4919_, v_isNeg_boxed_4932_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec_ref(v_a_4927_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec(v_a_4921_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4934_, lean_object* v_generation_4935_, lean_object* v_p_4936_, lean_object* v_lhs_4937_, lean_object* v_rhs_4938_, uint8_t v_isNeg_4939_, uint8_t v_isHEq_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
if (v_isNeg_4939_ == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_inc_ref(v_p_4936_);
v___x_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_p_4936_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc_ref(v_a_4947_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc(v_a_4941_);
lean_inc_ref(v___x_4952_);
lean_inc(v_generation_4935_);
lean_inc_ref(v_lhs_4937_);
v___x_4953_ = lean_grind_internalize(v_lhs_4937_, v_generation_4935_, v___x_4952_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref_known(v___x_4953_, 1);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc_ref(v_a_4947_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc(v_a_4941_);
lean_inc_ref(v_rhs_4938_);
v___x_4954_ = lean_grind_internalize(v_rhs_4938_, v_generation_4935_, v___x_4952_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec_ref_known(v___x_4954_, 1);
v___x_4955_ = lean_box(0);
v___x_4956_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4936_, v___x_4955_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4957_; 
lean_dec_ref_known(v___x_4956_, 1);
v___x_4957_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4937_, v_rhs_4938_, v_proof_4934_, v_isHEq_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
return v___x_4957_;
}
else
{
lean_dec_ref(v_rhs_4938_);
lean_dec_ref(v_lhs_4937_);
lean_dec_ref(v_proof_4934_);
return v___x_4956_;
}
}
else
{
lean_dec_ref(v_rhs_4938_);
lean_dec_ref(v_lhs_4937_);
lean_dec_ref(v_p_4936_);
lean_dec_ref(v_proof_4934_);
return v___x_4954_;
}
}
else
{
lean_dec_ref_known(v___x_4952_, 1);
lean_dec_ref(v_rhs_4938_);
lean_dec_ref(v_lhs_4937_);
lean_dec_ref(v_p_4936_);
lean_dec(v_generation_4935_);
lean_dec_ref(v_proof_4934_);
return v___x_4953_;
}
}
else
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
lean_dec_ref(v_rhs_4938_);
lean_dec_ref(v_lhs_4937_);
v___x_4958_ = lean_box(0);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc_ref(v_a_4947_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc(v_a_4941_);
lean_inc_ref(v_p_4936_);
v___x_4959_ = lean_grind_internalize(v_p_4936_, v_generation_4935_, v___x_4958_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v___x_4960_; 
lean_dec_ref_known(v___x_4959_, 1);
v___x_4960_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4945_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = l_Lean_Meta_mkEqFalse(v_proof_4934_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4936_, v_a_4961_, v_a_4963_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
return v___x_4964_;
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
lean_dec(v_a_4961_);
lean_dec_ref(v_p_4936_);
v_a_4965_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4962_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4962_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec_ref(v_p_4936_);
lean_dec_ref(v_proof_4934_);
v_a_4973_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4960_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4960_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_dec_ref(v_p_4936_);
lean_dec_ref(v_proof_4934_);
return v___x_4959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4981_ = _args[0];
lean_object* v_generation_4982_ = _args[1];
lean_object* v_p_4983_ = _args[2];
lean_object* v_lhs_4984_ = _args[3];
lean_object* v_rhs_4985_ = _args[4];
lean_object* v_isNeg_4986_ = _args[5];
lean_object* v_isHEq_4987_ = _args[6];
lean_object* v_a_4988_ = _args[7];
lean_object* v_a_4989_ = _args[8];
lean_object* v_a_4990_ = _args[9];
lean_object* v_a_4991_ = _args[10];
lean_object* v_a_4992_ = _args[11];
lean_object* v_a_4993_ = _args[12];
lean_object* v_a_4994_ = _args[13];
lean_object* v_a_4995_ = _args[14];
lean_object* v_a_4996_ = _args[15];
lean_object* v_a_4997_ = _args[16];
lean_object* v_a_4998_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4999_; uint8_t v_isHEq_boxed_5000_; lean_object* v_res_5001_; 
v_isNeg_boxed_4999_ = lean_unbox(v_isNeg_4986_);
v_isHEq_boxed_5000_ = lean_unbox(v_isHEq_4987_);
v_res_5001_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4981_, v_generation_4982_, v_p_4983_, v_lhs_4984_, v_rhs_4985_, v_isNeg_boxed_4999_, v_isHEq_boxed_5000_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec(v_a_4988_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_5005_, lean_object* v_generation_5006_, lean_object* v_p_5007_, uint8_t v_isNeg_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v___x_5020_; 
lean_inc_ref(v_p_5007_);
v___x_5020_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_5007_, v_a_5016_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref_known(v___x_5020_, 1);
v___x_5022_ = l_Lean_Expr_cleanupAnnotations(v_a_5021_);
lean_dec(v_a_5021_);
v___x_5023_ = l_Lean_Expr_isApp(v___x_5022_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; 
lean_dec_ref(v___x_5022_);
v___x_5024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5024_;
}
else
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5025_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5022_);
v___x_5026_ = l_Lean_Expr_isApp(v___x_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec_ref(v___x_5025_);
lean_dec_ref(v___x_5022_);
v___x_5027_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5027_;
}
else
{
lean_object* v___x_5028_; uint8_t v___x_5029_; 
v___x_5028_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5025_);
v___x_5029_ = l_Lean_Expr_isApp(v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; 
lean_dec_ref(v___x_5028_);
lean_dec_ref(v___x_5025_);
lean_dec_ref(v___x_5022_);
v___x_5030_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5030_;
}
else
{
lean_object* v_arg_5031_; lean_object* v_arg_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; uint8_t v___x_5035_; 
v_arg_5031_ = lean_ctor_get(v___x_5022_, 1);
lean_inc_ref(v_arg_5031_);
lean_dec_ref(v___x_5022_);
v_arg_5032_ = lean_ctor_get(v___x_5028_, 1);
lean_inc_ref(v_arg_5032_);
v___x_5033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5028_);
lean_dec_ref(v___x_5028_);
v___x_5034_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5035_ = l_Lean_Expr_isConstOf(v___x_5033_, v___x_5034_);
if (v___x_5035_ == 0)
{
uint8_t v___x_5036_; 
lean_dec_ref(v___x_5025_);
v___x_5036_ = l_Lean_Expr_isApp(v___x_5033_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; 
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_arg_5032_);
lean_dec_ref(v_arg_5031_);
v___x_5037_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5037_;
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v___x_5038_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5033_);
lean_dec_ref(v___x_5033_);
v___x_5039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5040_ = l_Lean_Expr_isConstOf(v___x_5038_, v___x_5039_);
lean_dec_ref(v___x_5038_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
lean_dec_ref(v_arg_5032_);
lean_dec_ref(v_arg_5031_);
v___x_5041_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5041_;
}
else
{
lean_object* v___x_5042_; 
v___x_5042_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5005_, v_generation_5006_, v_p_5007_, v_arg_5032_, v_arg_5031_, v_isNeg_5008_, v___x_5040_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5042_;
}
}
}
else
{
uint8_t v___x_5043_; 
lean_dec_ref(v___x_5033_);
v___x_5043_ = l_Lean_Expr_isProp(v_arg_5032_);
lean_dec_ref(v_arg_5032_);
if (v___x_5043_ == 0)
{
lean_object* v_arg_5044_; lean_object* v___x_5045_; 
v_arg_5044_ = lean_ctor_get(v___x_5025_, 1);
lean_inc_ref(v_arg_5044_);
lean_dec_ref(v___x_5025_);
v___x_5045_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5005_, v_generation_5006_, v_p_5007_, v_arg_5044_, v_arg_5031_, v_isNeg_5008_, v___x_5043_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5045_;
}
else
{
lean_object* v___x_5046_; 
lean_dec_ref(v_arg_5031_);
lean_dec_ref(v___x_5025_);
v___x_5046_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5005_, v_generation_5006_, v_p_5007_, v_isNeg_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5046_;
}
}
}
}
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec_ref(v_p_5007_);
lean_dec(v_generation_5006_);
lean_dec_ref(v_proof_5005_);
v_a_5047_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5020_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5020_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5055_, lean_object* v_generation_5056_, lean_object* v_p_5057_, lean_object* v_isNeg_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
uint8_t v_isNeg_boxed_5070_; lean_object* v_res_5071_; 
v_isNeg_boxed_5070_ = lean_unbox(v_isNeg_5058_);
v_res_5071_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5055_, v_generation_5056_, v_p_5057_, v_isNeg_boxed_5070_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec(v_a_5059_);
return v_res_5071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5080_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5081_ = l_Lean_Name_append(v___x_5080_, v___x_5079_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5082_, lean_object* v_proof_5083_, lean_object* v_generation_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___x_5127_; lean_object* v_toCold_5128_; lean_object* v_options_5129_; uint8_t v_hasTrace_5130_; 
lean_inc_ref(v_fact_5082_);
v___x_5127_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5082_, v_a_5085_);
lean_dec_ref(v___x_5127_);
v_toCold_5128_ = lean_ctor_get(v_a_5093_, 0);
v_options_5129_ = lean_ctor_get(v_toCold_5128_, 2);
v_hasTrace_5130_ = lean_ctor_get_uint8(v_options_5129_, sizeof(void*)*1);
if (v_hasTrace_5130_ == 0)
{
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
v___y_5116_ = v_a_5091_;
v___y_5117_ = v_a_5092_;
v___y_5118_ = v_a_5093_;
v___y_5119_ = v_a_5094_;
goto v___jp_5109_;
}
else
{
lean_object* v_inheritedTraceOptions_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; uint8_t v___x_5134_; 
v_inheritedTraceOptions_5131_ = lean_ctor_get(v_toCold_5128_, 11);
v___x_5132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5131_, v_options_5129_, v___x_5133_);
if (v___x_5134_ == 0)
{
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
v___y_5116_ = v_a_5091_;
v___y_5117_ = v_a_5092_;
v___y_5118_ = v_a_5093_;
v___y_5119_ = v_a_5094_;
goto v___jp_5109_;
}
else
{
lean_object* v___x_5135_; 
v___x_5135_ = l_Lean_Meta_Grind_updateLastTag(v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
lean_dec_ref_known(v___x_5135_, 1);
lean_inc_ref(v_fact_5082_);
v___x_5136_ = l_Lean_MessageData_ofExpr(v_fact_5082_);
v___x_5137_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5132_, v___x_5136_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_dec_ref_known(v___x_5137_, 1);
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
v___y_5116_ = v_a_5091_;
v___y_5117_ = v_a_5092_;
v___y_5118_ = v_a_5093_;
v___y_5119_ = v_a_5094_;
goto v___jp_5109_;
}
else
{
lean_dec(v_generation_5084_);
lean_dec_ref(v_proof_5083_);
lean_dec_ref(v_fact_5082_);
return v___x_5137_;
}
}
else
{
lean_dec(v_generation_5084_);
lean_dec_ref(v_proof_5083_);
lean_dec_ref(v_fact_5082_);
return v___x_5135_;
}
}
}
v___jp_5096_:
{
uint8_t v___x_5107_; lean_object* v___x_5108_; 
v___x_5107_ = 0;
v___x_5108_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5083_, v_generation_5084_, v_fact_5082_, v___x_5107_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5108_;
}
v___jp_5109_:
{
lean_object* v___x_5120_; uint8_t v___x_5121_; 
v___x_5120_ = l_Lean_Expr_cleanupAnnotations(v_fact_5082_);
v___x_5121_ = l_Lean_Expr_isApp(v___x_5120_);
if (v___x_5121_ == 0)
{
lean_dec_ref(v___x_5120_);
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
v___y_5101_ = v___y_5114_;
v___y_5102_ = v___y_5115_;
v___y_5103_ = v___y_5116_;
v___y_5104_ = v___y_5117_;
v___y_5105_ = v___y_5118_;
v___y_5106_ = v___y_5119_;
goto v___jp_5096_;
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; uint8_t v___x_5124_; 
v___x_5122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5120_);
v___x_5123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5124_ = l_Lean_Expr_isConstOf(v___x_5122_, v___x_5123_);
lean_dec_ref(v___x_5122_);
if (v___x_5124_ == 0)
{
lean_dec_ref(v___x_5120_);
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
v___y_5101_ = v___y_5114_;
v___y_5102_ = v___y_5115_;
v___y_5103_ = v___y_5116_;
v___y_5104_ = v___y_5117_;
v___y_5105_ = v___y_5118_;
v___y_5106_ = v___y_5119_;
goto v___jp_5096_;
}
else
{
lean_object* v_arg_5125_; lean_object* v___x_5126_; 
lean_dec_ref(v_fact_5082_);
v_arg_5125_ = lean_ctor_get(v___x_5120_, 1);
lean_inc_ref(v_arg_5125_);
lean_dec_ref(v___x_5120_);
v___x_5126_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5083_, v_generation_5084_, v_arg_5125_, v___x_5124_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
return v___x_5126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5138_, lean_object* v_proof_5139_, lean_object* v_generation_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5138_, v_proof_5139_, v_generation_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_a_5144_);
lean_dec_ref(v_a_5143_);
lean_dec(v_a_5142_);
lean_dec(v_a_5141_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5156_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; uint8_t v___x_5169_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
v___x_5169_ = lean_unbox(v_a_5168_);
if (v___x_5169_ == 0)
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5170_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5171_ = l_Lean_Core_checkSystem(v___x_5170_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v___x_5172_; 
lean_dec_ref_known(v___x_5171_, 1);
v___x_5172_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5156_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5271_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5271_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5271_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
if (lean_obj_tag(v_a_5173_) == 1)
{
lean_object* v_val_5177_; 
lean_del_object(v___x_5175_);
v_val_5177_ = lean_ctor_get(v_a_5173_, 0);
lean_inc(v_val_5177_);
lean_dec_ref_known(v_a_5173_, 1);
switch(lean_obj_tag(v_val_5177_))
{
case 0:
{
lean_object* v_lhs_5178_; lean_object* v_rhs_5179_; lean_object* v_proof_5180_; uint8_t v_isHEq_5181_; lean_object* v___x_5182_; 
lean_dec(v_a_5168_);
v_lhs_5178_ = lean_ctor_get(v_val_5177_, 0);
lean_inc_ref(v_lhs_5178_);
v_rhs_5179_ = lean_ctor_get(v_val_5177_, 1);
lean_inc_ref(v_rhs_5179_);
v_proof_5180_ = lean_ctor_get(v_val_5177_, 2);
lean_inc_ref(v_proof_5180_);
v_isHEq_5181_ = lean_ctor_get_uint8(v_val_5177_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5177_, 3);
v___x_5182_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5178_, v_rhs_5179_, v_proof_5180_, v_isHEq_5181_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
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
case 1:
{
lean_object* v_prop_5192_; lean_object* v_proof_5193_; lean_object* v_generation_5194_; lean_object* v___x_5195_; 
lean_dec(v_a_5168_);
v_prop_5192_ = lean_ctor_get(v_val_5177_, 0);
lean_inc_ref(v_prop_5192_);
v_proof_5193_ = lean_ctor_get(v_val_5177_, 1);
lean_inc_ref(v_proof_5193_);
v_generation_5194_ = lean_ctor_get(v_val_5177_, 2);
lean_inc(v_generation_5194_);
lean_dec_ref_known(v_val_5177_, 3);
v___x_5195_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5192_, v_proof_5193_, v_generation_5194_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
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
case 2:
{
lean_object* v_e_5205_; lean_object* v___x_5206_; 
lean_dec(v_a_5168_);
v_e_5205_ = lean_ctor_get(v_val_5177_, 0);
lean_inc_ref(v_e_5205_);
lean_dec_ref_known(v_val_5177_, 1);
v___x_5206_ = l_Lean_Meta_Grind_propagateUp(v_e_5205_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
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
case 3:
{
lean_object* v_lhs_5216_; lean_object* v_rhs_5217_; lean_object* v_proof_5218_; lean_object* v_generation_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
v_lhs_5216_ = lean_ctor_get(v_val_5177_, 0);
lean_inc_ref(v_lhs_5216_);
v_rhs_5217_ = lean_ctor_get(v_val_5177_, 1);
lean_inc_ref_n(v_rhs_5217_, 2);
v_proof_5218_ = lean_ctor_get(v_val_5177_, 2);
lean_inc_ref(v_proof_5218_);
v_generation_5219_ = lean_ctor_get(v_val_5177_, 3);
lean_inc(v_generation_5219_);
lean_dec_ref_known(v_val_5177_, 4);
v___x_5220_ = lean_box(0);
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
lean_inc(v___y_5161_);
lean_inc_ref(v___y_5160_);
lean_inc(v___y_5159_);
lean_inc_ref(v___y_5158_);
lean_inc(v___y_5157_);
lean_inc(v___y_5156_);
v___x_5221_ = lean_grind_internalize(v_rhs_5217_, v_generation_5219_, v___x_5220_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5221_) == 0)
{
uint8_t v___x_5222_; lean_object* v___x_5223_; 
lean_dec_ref_known(v___x_5221_, 1);
v___x_5222_ = lean_unbox(v_a_5168_);
lean_dec(v_a_5168_);
v___x_5223_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5216_, v_rhs_5217_, v_proof_5218_, v___x_5222_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_dec_ref_known(v___x_5223_, 1);
goto _start;
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
v_a_5225_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5223_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5223_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_dec_ref(v_proof_5218_);
lean_dec_ref(v_rhs_5217_);
lean_dec_ref(v_lhs_5216_);
lean_dec(v_a_5168_);
v_a_5233_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5221_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5221_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
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
case 4:
{
lean_object* v_solverId_5241_; lean_object* v_lhs_5242_; lean_object* v_rhs_5243_; lean_object* v___x_5244_; 
lean_dec(v_a_5168_);
v_solverId_5241_ = lean_ctor_get(v_val_5177_, 0);
lean_inc(v_solverId_5241_);
v_lhs_5242_ = lean_ctor_get(v_val_5177_, 1);
lean_inc_ref(v_lhs_5242_);
v_rhs_5243_ = lean_ctor_get(v_val_5177_, 2);
lean_inc_ref(v_rhs_5243_);
lean_dec_ref_known(v_val_5177_, 3);
v___x_5244_ = l_Lean_Meta_Grind_Solvers_newEq(v_solverId_5241_, v_lhs_5242_, v_rhs_5243_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v_solverId_5241_);
if (lean_obj_tag(v___x_5244_) == 0)
{
lean_dec_ref_known(v___x_5244_, 1);
goto _start;
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
v_a_5246_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5244_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5244_);
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
default: 
{
lean_object* v_solverId_5254_; lean_object* v_lhs_5255_; lean_object* v_rhs_5256_; lean_object* v___x_5257_; 
lean_dec(v_a_5168_);
v_solverId_5254_ = lean_ctor_get(v_val_5177_, 0);
lean_inc(v_solverId_5254_);
v_lhs_5255_ = lean_ctor_get(v_val_5177_, 1);
lean_inc_ref(v_lhs_5255_);
v_rhs_5256_ = lean_ctor_get(v_val_5177_, 2);
lean_inc_ref(v_rhs_5256_);
lean_dec_ref_known(v_val_5177_, 3);
v___x_5257_ = l_Lean_Meta_Grind_Solvers_newDiseq(v_solverId_5254_, v_lhs_5255_, v_rhs_5256_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v_solverId_5254_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_dec_ref_known(v___x_5257_, 1);
goto _start;
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5259_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5257_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5257_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
}
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5269_; 
lean_dec(v_a_5173_);
lean_dec(v_a_5168_);
v___x_5267_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5267_);
v___x_5269_ = v___x_5175_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v___x_5267_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_dec(v_a_5168_);
v_a_5272_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5172_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5172_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec(v_a_5168_);
v_a_5280_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___x_5171_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5171_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
else
{
lean_object* v___x_5288_; 
lean_dec(v_a_5168_);
v___x_5288_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5156_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5296_; 
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5296_ == 0)
{
lean_object* v_unused_5297_; 
v_unused_5297_ = lean_ctor_get(v___x_5288_, 0);
lean_dec(v_unused_5297_);
v___x_5290_ = v___x_5288_;
v_isShared_5291_ = v_isSharedCheck_5296_;
goto v_resetjp_5289_;
}
else
{
lean_dec(v___x_5288_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5296_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5292_; lean_object* v___x_5294_; 
v___x_5292_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5292_);
v___x_5294_ = v___x_5290_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v___x_5292_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
v_a_5298_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5288_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5288_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
v_a_5306_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5167_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5167_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec(v___y_5314_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_to_do(lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5337_ = lean_box(0);
v___x_5338_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
lean_dec(v_a_5331_);
lean_dec_ref(v_a_5330_);
lean_dec(v_a_5329_);
lean_dec_ref(v_a_5328_);
lean_dec(v_a_5327_);
lean_dec(v_a_5326_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5351_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5341_ = v___x_5338_;
v_isShared_5342_ = v_isSharedCheck_5351_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5338_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5351_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v_fst_5343_; 
v_fst_5343_ = lean_ctor_get(v_a_5339_, 0);
lean_inc(v_fst_5343_);
lean_dec(v_a_5339_);
if (lean_obj_tag(v_fst_5343_) == 0)
{
lean_object* v___x_5345_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5337_);
v___x_5345_ = v___x_5341_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5337_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
else
{
lean_object* v_val_5347_; lean_object* v___x_5349_; 
v_val_5347_ = lean_ctor_get(v_fst_5343_, 0);
lean_inc(v_val_5347_);
lean_dec_ref_known(v_fst_5343_, 1);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v_val_5347_);
v___x_5349_ = v___x_5341_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_val_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
v_a_5352_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5338_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5338_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = lean_grind_process_to_do(v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5372_, lean_object* v_a_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5386_, lean_object* v_a_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5386_, v_a_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v_a_5387_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5400_, lean_object* v_proof_5401_, lean_object* v_generation_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
uint8_t v___x_5414_; 
v___x_5414_ = l_Lean_Expr_isTrue(v_fact_5400_);
if (v___x_5414_ == 0)
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5403_);
if (lean_obj_tag(v___x_5415_) == 0)
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5446_; 
v_a_5416_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5418_ = v___x_5415_;
v_isShared_5419_ = v_isSharedCheck_5446_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5415_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5446_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
uint8_t v___x_5420_; 
v___x_5420_ = lean_unbox(v_a_5416_);
lean_dec(v_a_5416_);
if (v___x_5420_ == 0)
{
lean_object* v___x_5421_; 
lean_del_object(v___x_5418_);
lean_inc(v_a_5412_);
lean_inc_ref(v_a_5411_);
lean_inc(v_a_5410_);
lean_inc_ref(v_a_5409_);
lean_inc(v_a_5408_);
lean_inc_ref(v_a_5407_);
lean_inc(v_a_5406_);
lean_inc_ref(v_a_5405_);
lean_inc(v_a_5404_);
lean_inc(v_a_5403_);
v___x_5421_ = lean_grind_process_to_do(v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v___x_5422_; 
lean_dec_ref_known(v___x_5421_, 1);
v___x_5422_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5403_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5433_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5425_ = v___x_5422_;
v_isShared_5426_ = v_isSharedCheck_5433_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5422_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5433_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
uint8_t v___x_5427_; 
v___x_5427_ = lean_unbox(v_a_5423_);
lean_dec(v_a_5423_);
if (v___x_5427_ == 0)
{
lean_object* v___x_5428_; 
lean_del_object(v___x_5425_);
v___x_5428_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5400_, v_proof_5401_, v_generation_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_);
return v___x_5428_;
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5431_; 
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
v___x_5429_ = lean_box(0);
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 0, v___x_5429_);
v___x_5431_ = v___x_5425_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v___x_5429_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
else
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5441_; 
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
v_a_5434_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5436_ = v___x_5422_;
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5422_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5439_; 
if (v_isShared_5437_ == 0)
{
v___x_5439_ = v___x_5436_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_a_5434_);
v___x_5439_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
return v___x_5439_;
}
}
}
}
else
{
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
return v___x_5421_;
}
}
else
{
lean_object* v___x_5442_; lean_object* v___x_5444_; 
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
v___x_5442_ = lean_box(0);
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 0, v___x_5442_);
v___x_5444_ = v___x_5418_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5442_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
v_a_5447_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5415_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5415_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
lean_dec(v_generation_5402_);
lean_dec_ref(v_proof_5401_);
lean_dec_ref(v_fact_5400_);
v___x_5455_ = lean_box(0);
v___x_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5456_, 0, v___x_5455_);
return v___x_5456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5457_, lean_object* v_proof_5458_, lean_object* v_generation_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v_res_5471_; 
v_res_5471_ = l_Lean_Meta_Grind_add(v_fact_5457_, v_proof_5458_, v_generation_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_);
lean_dec(v_a_5469_);
lean_dec_ref(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec(v_a_5460_);
return v_res_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5472_, lean_object* v_generation_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_){
_start:
{
lean_object* v___x_5485_; 
lean_inc(v_fvarId_5472_);
v___x_5485_ = l_Lean_FVarId_getType___redArg(v_fvarId_5472_, v_a_5480_, v_a_5482_, v_a_5483_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref_known(v___x_5485_, 1);
v___x_5487_ = l_Lean_mkFVar(v_fvarId_5472_);
v___x_5488_ = l_Lean_Meta_Grind_add(v_a_5486_, v___x_5487_, v_generation_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_);
return v___x_5488_;
}
else
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5496_; 
lean_dec(v_generation_5473_);
lean_dec(v_fvarId_5472_);
v_a_5489_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5491_ = v___x_5485_;
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5485_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5494_; 
if (v_isShared_5492_ == 0)
{
v___x_5494_ = v___x_5491_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5497_, lean_object* v_generation_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_){
_start:
{
lean_object* v_res_5510_; 
v_res_5510_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5497_, v_generation_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
lean_dec(v_a_5508_);
lean_dec_ref(v_a_5507_);
lean_dec(v_a_5506_);
lean_dec_ref(v_a_5505_);
lean_dec(v_a_5504_);
lean_dec_ref(v_a_5503_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec(v_a_5499_);
return v_res_5510_;
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
