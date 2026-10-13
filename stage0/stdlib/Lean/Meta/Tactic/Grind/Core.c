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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
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
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_DelayedTheoremInstance_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object*);
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getEqc(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ENode_isCongrRoot(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Solvers_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 181, 250, 47, 64, 71, 92, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_22641__boxed_359_; lean_object* v_res_360_; 
v_x_22641__boxed_359_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_res_360_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_355_, v_x_356_, v_x_22641__boxed_359_, v_x_358_);
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
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v___x_403_; lean_object* v___y_405_; uint8_t v_a_445_; uint8_t v___x_459_; 
v_head_401_ = lean_ctor_get(v_as_x27_387_, 0);
v_tail_402_ = lean_ctor_get(v_as_x27_387_, 1);
v___x_403_ = lean_box(0);
v___x_459_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_401_);
if (v___x_459_ == 0)
{
v_a_445_ = v___x_459_;
goto v___jp_444_;
}
else
{
lean_object* v___x_460_; 
lean_inc(v_head_401_);
v___x_460_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_401_, v___y_389_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; uint8_t v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = lean_unbox(v_a_461_);
lean_dec(v_a_461_);
v_a_445_ = v___x_462_;
goto v___jp_444_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_460_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_460_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v_toGoalState_407_; lean_object* v_mvarId_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_443_; 
v___x_406_ = lean_st_ref_take(v___y_405_);
v_toGoalState_407_ = lean_ctor_get(v___x_406_, 0);
v_mvarId_408_ = lean_ctor_get(v___x_406_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_443_ == 0)
{
v___x_410_ = v___x_406_;
v_isShared_411_ = v_isSharedCheck_443_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_mvarId_408_);
lean_inc(v_toGoalState_407_);
lean_dec(v___x_406_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_443_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_nextDeclIdx_412_; lean_object* v_enodeMap_413_; lean_object* v_exprs_414_; lean_object* v_parents_415_; lean_object* v_congrTable_416_; lean_object* v_appMap_417_; lean_object* v_indicesFound_418_; lean_object* v_newFacts_419_; uint8_t v_inconsistent_420_; lean_object* v_nextIdx_421_; lean_object* v_newRawFacts_422_; lean_object* v_facts_423_; lean_object* v_extThms_424_; lean_object* v_ematch_425_; lean_object* v_inj_426_; lean_object* v_split_427_; lean_object* v_clean_428_; lean_object* v_sstates_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_442_; 
v_nextDeclIdx_412_ = lean_ctor_get(v_toGoalState_407_, 0);
v_enodeMap_413_ = lean_ctor_get(v_toGoalState_407_, 1);
v_exprs_414_ = lean_ctor_get(v_toGoalState_407_, 2);
v_parents_415_ = lean_ctor_get(v_toGoalState_407_, 3);
v_congrTable_416_ = lean_ctor_get(v_toGoalState_407_, 4);
v_appMap_417_ = lean_ctor_get(v_toGoalState_407_, 5);
v_indicesFound_418_ = lean_ctor_get(v_toGoalState_407_, 6);
v_newFacts_419_ = lean_ctor_get(v_toGoalState_407_, 7);
v_inconsistent_420_ = lean_ctor_get_uint8(v_toGoalState_407_, sizeof(void*)*17);
v_nextIdx_421_ = lean_ctor_get(v_toGoalState_407_, 8);
v_newRawFacts_422_ = lean_ctor_get(v_toGoalState_407_, 9);
v_facts_423_ = lean_ctor_get(v_toGoalState_407_, 10);
v_extThms_424_ = lean_ctor_get(v_toGoalState_407_, 11);
v_ematch_425_ = lean_ctor_get(v_toGoalState_407_, 12);
v_inj_426_ = lean_ctor_get(v_toGoalState_407_, 13);
v_split_427_ = lean_ctor_get(v_toGoalState_407_, 14);
v_clean_428_ = lean_ctor_get(v_toGoalState_407_, 15);
v_sstates_429_ = lean_ctor_get(v_toGoalState_407_, 16);
v_isSharedCheck_442_ = !lean_is_exclusive(v_toGoalState_407_);
if (v_isSharedCheck_442_ == 0)
{
v___x_431_ = v_toGoalState_407_;
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_sstates_429_);
lean_inc(v_clean_428_);
lean_inc(v_split_427_);
lean_inc(v_inj_426_);
lean_inc(v_ematch_425_);
lean_inc(v_extThms_424_);
lean_inc(v_facts_423_);
lean_inc(v_newRawFacts_422_);
lean_inc(v_nextIdx_421_);
lean_inc(v_newFacts_419_);
lean_inc(v_indicesFound_418_);
lean_inc(v_appMap_417_);
lean_inc(v_congrTable_416_);
lean_inc(v_parents_415_);
lean_inc(v_exprs_414_);
lean_inc(v_enodeMap_413_);
lean_inc(v_nextDeclIdx_412_);
lean_dec(v_toGoalState_407_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_head_401_);
v___x_433_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_413_, v_congrTable_416_, v_head_401_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 4, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_nextDeclIdx_412_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_enodeMap_413_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_exprs_414_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_parents_415_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_appMap_417_);
lean_ctor_set(v_reuseFailAlloc_441_, 6, v_indicesFound_418_);
lean_ctor_set(v_reuseFailAlloc_441_, 7, v_newFacts_419_);
lean_ctor_set(v_reuseFailAlloc_441_, 8, v_nextIdx_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 9, v_newRawFacts_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 10, v_facts_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 11, v_extThms_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 12, v_ematch_425_);
lean_ctor_set(v_reuseFailAlloc_441_, 13, v_inj_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 14, v_split_427_);
lean_ctor_set(v_reuseFailAlloc_441_, 15, v_clean_428_);
lean_ctor_set(v_reuseFailAlloc_441_, 16, v_sstates_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*17, v_inconsistent_420_);
v___x_435_ = v_reuseFailAlloc_441_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_435_);
v___x_437_ = v___x_410_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_mvarId_408_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; 
v___x_438_ = lean_st_ref_put(v___y_405_, v___x_437_);
v_as_x27_387_ = v_tail_402_;
v_b_388_ = v___x_403_;
goto _start;
}
}
}
}
}
v___jp_444_:
{
if (v_a_445_ == 0)
{
v_as_x27_387_ = v_tail_402_;
v_b_388_ = v___x_403_;
goto _start;
}
else
{
lean_object* v_toCold_447_; lean_object* v_options_448_; uint8_t v_hasTrace_449_; 
v_toCold_447_ = lean_ctor_get(v___y_397_, 0);
v_options_448_ = lean_ctor_get(v_toCold_447_, 2);
v_hasTrace_449_ = lean_ctor_get_uint8(v_options_448_, sizeof(void*)*1);
if (v_hasTrace_449_ == 0)
{
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
lean_object* v_inheritedTraceOptions_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_inheritedTraceOptions_450_ = lean_ctor_get(v_toCold_447_, 11);
v___x_451_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_452_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_450_, v_options_448_, v___x_452_);
if (v___x_453_ == 0)
{
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_updateLastTag(v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref_known(v___x_454_, 1);
v___x_455_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_401_);
v___x_456_ = l_Lean_MessageData_ofExpr(v_head_401_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_451_, v___x_457_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_dec_ref_known(v___x_458_, 1);
v___y_405_ = v___y_389_;
goto v___jp_404_;
}
else
{
return v___x_458_;
}
}
else
{
return v___x_454_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_471_, v_b_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v_as_x27_471_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Meta_Grind_getParents___redArg(v_root_485_, v_a_486_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_498_);
v___x_500_ = lean_box(0);
v___x_501_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_499_, v___x_500_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v___x_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_509_);
v___x_503_ = v___x_501_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v_a_498_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_498_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_a_498_);
v_a_510_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_501_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_root_518_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_531_, lean_object* v_00_u03b2_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_531_, v_x_533_, v_x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_536_, lean_object* v_00_u03b2_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_536_, v_00_u03b2_537_, v_x_538_, v_x_539_);
lean_dec_ref(v___x_536_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_541_, v_msg_542_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_555_, v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec(v___y_557_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_569_, lean_object* v_as_x27_570_, lean_object* v_b_571_, lean_object* v_a_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_570_, v_b_571_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_585_, lean_object* v_as_x27_586_, lean_object* v_b_587_, lean_object* v_a_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_585_, v_as_x27_586_, v_b_587_, v_a_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
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
lean_dec(v_as_x27_586_);
lean_dec(v_as_585_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_601_, lean_object* v_00_u03b2_602_, lean_object* v_x_603_, size_t v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_601_, v_x_603_, v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_607_, lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
size_t v_x_23103__boxed_612_; lean_object* v_res_613_; 
v_x_23103__boxed_612_ = lean_unbox_usize(v_x_610_);
lean_dec(v_x_610_);
v_res_613_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_607_, v_00_u03b2_608_, v_x_609_, v_x_23103__boxed_612_, v_x_611_);
lean_dec_ref(v___x_607_);
return v_res_613_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_616_ = l_Lean_stringToMessageData(v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
if (lean_obj_tag(v_as_x27_617_) == 0)
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_b_618_);
return v___x_630_;
}
else
{
lean_object* v_head_631_; lean_object* v_tail_632_; lean_object* v___x_633_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; uint8_t v_a_648_; uint8_t v___x_662_; 
v_head_631_ = lean_ctor_get(v_as_x27_617_, 0);
v_tail_632_ = lean_ctor_get(v_as_x27_617_, 1);
v___x_633_ = lean_box(0);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_631_);
if (v___x_662_ == 0)
{
v_a_648_ = v___x_662_;
goto v___jp_647_;
}
else
{
lean_object* v___x_663_; 
lean_inc(v_head_631_);
v___x_663_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_631_, v___y_619_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; uint8_t v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_unbox(v_a_664_);
lean_dec(v_a_664_);
v_a_648_ = v___x_665_;
goto v___jp_647_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_663_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_663_);
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
v___jp_634_:
{
lean_object* v___x_645_; 
lean_inc(v_head_631_);
v___x_645_ = l_Lean_Meta_Grind_addCongrTable(v_head_631_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref_known(v___x_645_, 1);
v_as_x27_617_ = v_tail_632_;
v_b_618_ = v___x_633_;
goto _start;
}
else
{
return v___x_645_;
}
}
v___jp_647_:
{
if (v_a_648_ == 0)
{
v_as_x27_617_ = v_tail_632_;
v_b_618_ = v___x_633_;
goto _start;
}
else
{
lean_object* v_toCold_650_; lean_object* v_options_651_; uint8_t v_hasTrace_652_; 
v_toCold_650_ = lean_ctor_get(v___y_627_, 0);
v_options_651_ = lean_ctor_get(v_toCold_650_, 2);
v_hasTrace_652_ = lean_ctor_get_uint8(v_options_651_, sizeof(void*)*1);
if (v_hasTrace_652_ == 0)
{
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
goto v___jp_634_;
}
else
{
lean_object* v_inheritedTraceOptions_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_inheritedTraceOptions_653_ = lean_ctor_get(v_toCold_650_, 11);
v___x_654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_655_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_656_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_653_, v_options_651_, v___x_655_);
if (v___x_656_ == 0)
{
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
goto v___jp_634_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Grind_updateLastTag(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec_ref_known(v___x_657_, 1);
v___x_658_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_631_);
v___x_659_ = l_Lean_MessageData_ofExpr(v_head_631_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_654_, v___x_660_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
v___y_642_ = v___y_626_;
v___y_643_ = v___y_627_;
v___y_644_ = v___y_628_;
goto v___jp_634_;
}
else
{
return v___x_661_;
}
}
else
{
return v___x_657_;
}
}
}
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
v_ematch_1132_ = lean_ctor_get(v_toGoalState_1131_, 12);
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
lean_dec_ref(v_fn_1249_);
lean_dec_ref_known(v_snd_1231_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2030_, lean_object* v_lams_u2081_2031_, lean_object* v_as_2032_, size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
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
lean_object* v_binderType_2056_; lean_object* v_body_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_binderType_2056_ = lean_ctor_get(v_a_2055_, 1);
v_body_2057_ = lean_ctor_get(v_a_2055_, 2);
v___x_2058_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2056_);
v___x_2059_ = l_Lean_Meta_getLevel(v_binderType_2056_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_a_2060_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
lean_inc_ref(v___x_2063_);
v___x_2064_ = l_Lean_mkConst(v___x_2061_, v___x_2063_);
lean_inc_ref(v_binderType_2056_);
v___x_2065_ = l_Lean_Expr_app___override(v___x_2064_, v_binderType_2056_);
v___x_2066_ = lean_box(0);
v___x_2067_ = l_Lean_Meta_synthInstance_x3f(v___x_2065_, v___x_2066_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
if (lean_obj_tag(v_a_2068_) == 1)
{
lean_object* v_val_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; uint8_t v___x_2134_; 
v_val_2069_ = lean_ctor_get(v_a_2068_, 0);
lean_inc(v_val_2069_);
lean_dec_ref_known(v_a_2068_, 1);
v___x_2134_ = l_Lean_Expr_hasLooseBVars(v_body_2057_);
if (v___x_2134_ == 0)
{
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2063_);
v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2063_);
lean_inc_ref(v_binderType_2056_);
v___x_2137_ = l_Lean_Expr_app___override(v___x_2136_, v_binderType_2056_);
v___x_2138_ = l_Lean_Meta_synthInstance_x3f(v___x_2137_, v___x_2066_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
if (lean_obj_tag(v_a_2139_) == 0)
{
lean_dec(v_val_2069_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
lean_dec_ref_known(v_a_2139_, 1);
if (v___x_2134_ == 0)
{
lean_dec(v_val_2069_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
goto v___jp_2070_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_val_2069_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2140_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2138_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2138_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
v___jp_2070_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2030_, v_binderType_2056_);
if (lean_obj_tag(v___x_2081_) == 1)
{
lean_object* v_val_2082_; 
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v_val_2082_) == 6)
{
lean_object* v_binderType_2083_; lean_object* v_body_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_binderType_2083_ = lean_ctor_get(v_val_2082_, 1);
lean_inc_ref(v_binderType_2083_);
v_body_2084_ = lean_ctor_get(v_val_2082_, 2);
lean_inc_ref(v_body_2084_);
lean_dec_ref_known(v_val_2082_, 3);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2086_ = l_Lean_mkConst(v___x_2085_, v___x_2063_);
v___x_2087_ = l_Lean_mkAppB(v___x_2086_, v_binderType_2083_, v_val_2069_);
v___x_2088_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2087_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = lean_expr_instantiate1(v_body_2057_, v_a_2089_);
v___x_2091_ = lean_expr_instantiate1(v_body_2084_, v_a_2089_);
lean_dec_ref(v_body_2084_);
v___x_2092_ = lean_array_fget_borrowed(v_lams_u2081_2031_, v___x_2058_);
v___x_2093_ = lean_array_fget_borrowed(v_lams_u2082_2030_, v___x_2058_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc(v___x_2093_);
lean_inc(v___x_2092_);
v___x_2094_ = lean_grind_mk_eq_proof(v___x_2092_, v___x_2093_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_mkCongrFun(v_a_2095_, v_a_2089_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_Meta_mkEq(v___x_2090_, v___x_2091_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = l_Lean_Meta_mkExpectedPropHint(v_a_2097_, v_a_2099_);
v___x_2101_ = l_Lean_Meta_Grind_pushNewFact(v___x_2100_, v___x_2058_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref_known(v___x_2101_, 1);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
return v___x_2101_;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2097_);
v_a_2102_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2098_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2098_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2090_);
v_a_2110_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2096_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2096_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2090_);
lean_dec(v_a_2089_);
v_a_2118_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2094_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2094_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_body_2084_);
v_a_2126_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2088_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2088_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_dec(v_val_2082_);
lean_dec(v_val_2069_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_dec(v___x_2081_);
lean_dec(v_val_2069_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
}
else
{
lean_dec(v_a_2068_);
lean_dec_ref_known(v___x_2063_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref_known(v___x_2063_, 2);
v_a_2148_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2067_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2067_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
v_a_2156_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2059_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2059_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2164_ = _args[0];
lean_object* v_lams_u2081_2165_ = _args[1];
lean_object* v_as_2166_ = _args[2];
lean_object* v_sz_2167_ = _args[3];
lean_object* v_i_2168_ = _args[4];
lean_object* v_b_2169_ = _args[5];
lean_object* v___y_2170_ = _args[6];
lean_object* v___y_2171_ = _args[7];
lean_object* v___y_2172_ = _args[8];
lean_object* v___y_2173_ = _args[9];
lean_object* v___y_2174_ = _args[10];
lean_object* v___y_2175_ = _args[11];
lean_object* v___y_2176_ = _args[12];
lean_object* v___y_2177_ = _args[13];
lean_object* v___y_2178_ = _args[14];
lean_object* v___y_2179_ = _args[15];
lean_object* v___y_2180_ = _args[16];
_start:
{
size_t v_sz_boxed_2181_; size_t v_i_boxed_2182_; lean_object* v_res_2183_; 
v_sz_boxed_2181_ = lean_unbox_usize(v_sz_2167_);
lean_dec(v_sz_2167_);
v_i_boxed_2182_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2164_, v_lams_u2081_2165_, v_as_2166_, v_sz_boxed_2181_, v_i_boxed_2182_, v_b_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v_as_2166_);
lean_dec_ref(v_lams_u2081_2165_);
lean_dec_ref(v_lams_u2082_2164_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2184_, lean_object* v_lams_u2082_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = lean_array_get_size(v_lams_u2081_2184_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_nat_dec_eq(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_array_get_size(v_lams_u2082_2185_);
v___x_2201_ = lean_nat_dec_eq(v___x_2200_, v___x_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v_sz_2203_ = lean_array_size(v_lams_u2081_2184_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2185_, v_lams_u2081_2184_, v_lams_u2081_2184_, v_sz_2203_, v___x_2204_, v___x_2202_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2202_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2202_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
return v___x_2205_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2218_, lean_object* v_lams_u2082_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2218_, v_lams_u2082_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_lams_u2082_2219_);
lean_dec_ref(v_lams_u2081_2218_);
return v_res_2231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2234_);
lean_dec_ref(v_x_2234_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2237_, lean_object* v_x_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_x_2241_){
_start:
{
uint8_t v_res_2242_; lean_object* v_r_2243_; 
v_res_2242_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2240_, v_x_2241_);
lean_dec_ref(v_x_2241_);
v_r_2243_ = lean_box(v_res_2242_);
return v_r_2243_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2244_, lean_object* v_v_2245_, lean_object* v_i_2246_){
_start:
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_array_get_size(v_xs_2244_);
v___x_2248_ = lean_nat_dec_lt(v_i_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec(v_i_2246_);
v___x_2249_ = lean_box(0);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2250_ = lean_array_fget_borrowed(v_xs_2244_, v_i_2246_);
v___x_2251_ = lean_ptr_addr(v___x_2250_);
v___x_2252_ = lean_ptr_addr(v_v_2245_);
v___x_2253_ = lean_usize_dec_eq(v___x_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v_i_2246_, v___x_2254_);
lean_dec(v_i_2246_);
v_i_2246_ = v___x_2255_;
goto _start;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_i_2246_);
return v___x_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2258_, lean_object* v_v_2259_, lean_object* v_i_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2258_, v_v_2259_, v_i_2260_);
lean_dec_ref(v_v_2259_);
lean_dec_ref(v_xs_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2262_, lean_object* v_v_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2262_, v_v_2263_, v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2266_, lean_object* v_v_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2266_, v_v_2267_);
lean_dec_ref(v_v_2267_);
lean_dec_ref(v_xs_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2269_, size_t v_x_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 0)
{
lean_object* v_es_2272_; lean_object* v___x_2273_; size_t v___x_2274_; size_t v___x_2275_; lean_object* v_j_2276_; lean_object* v_entry_2277_; 
v_es_2272_ = lean_ctor_get(v_x_2269_, 0);
v___x_2273_ = lean_box(2);
v___x_2274_ = ((size_t)31ULL);
v___x_2275_ = lean_usize_land(v_x_2270_, v___x_2274_);
v_j_2276_ = lean_usize_to_nat(v___x_2275_);
v_entry_2277_ = lean_array_get(v___x_2273_, v_es_2272_, v_j_2276_);
switch(lean_obj_tag(v_entry_2277_))
{
case 0:
{
lean_object* v_key_2278_; size_t v___x_2279_; size_t v___x_2280_; uint8_t v___x_2281_; 
v_key_2278_ = lean_ctor_get(v_entry_2277_, 0);
lean_inc(v_key_2278_);
lean_dec_ref_known(v_entry_2277_, 2);
v___x_2279_ = lean_ptr_addr(v_x_2271_);
v___x_2280_ = lean_ptr_addr(v_key_2278_);
lean_dec(v_key_2278_);
v___x_2281_ = lean_usize_dec_eq(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v_j_2276_);
return v_x_2269_;
}
else
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
lean_inc_ref(v_es_2272_);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_x_2269_, 0);
lean_dec(v_unused_2290_);
v___x_2283_ = v_x_2269_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v_x_2269_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_array_set(v_es_2272_, v_j_2276_, v___x_2273_);
lean_dec(v_j_2276_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
case 1:
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2325_; 
lean_inc_ref(v_es_2272_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_x_2269_, 0);
lean_dec(v_unused_2326_);
v___x_2292_ = v_x_2269_;
v_isShared_2293_ = v_isSharedCheck_2325_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_x_2269_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2325_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_node_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2324_; 
v_node_2294_ = lean_ctor_get(v_entry_2277_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_entry_2277_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2296_ = v_entry_2277_;
v_isShared_2297_ = v_isSharedCheck_2324_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_node_2294_);
lean_dec(v_entry_2277_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2324_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
size_t v___x_2298_; lean_object* v_entries_2299_; size_t v___x_2300_; lean_object* v_newNode_2301_; lean_object* v___x_2302_; 
v___x_2298_ = ((size_t)5ULL);
v_entries_2299_ = lean_array_set(v_es_2272_, v_j_2276_, v___x_2273_);
v___x_2300_ = lean_usize_shift_right(v_x_2270_, v___x_2298_);
v_newNode_2301_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2294_, v___x_2300_, v_x_2271_);
lean_inc_ref(v_newNode_2301_);
v___x_2302_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2304_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_newNode_2301_);
v___x_2304_ = v___x_2296_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_newNode_2301_);
v___x_2304_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = lean_array_set(v_entries_2299_, v_j_2276_, v___x_2304_);
lean_dec(v_j_2276_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2305_);
v___x_2307_ = v___x_2292_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_val_2310_; lean_object* v_fst_2311_; lean_object* v_snd_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_newNode_2301_);
lean_del_object(v___x_2296_);
v_val_2310_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v___x_2302_, 1);
v_fst_2311_ = lean_ctor_get(v_val_2310_, 0);
v_snd_2312_ = lean_ctor_get(v_val_2310_, 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_val_2310_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2314_ = v_val_2310_;
v_isShared_2315_ = v_isSharedCheck_2323_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_snd_2312_);
lean_inc(v_fst_2311_);
lean_dec(v_val_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2323_;
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
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_fst_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_snd_2312_);
v___x_2317_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = lean_array_set(v_entries_2299_, v_j_2276_, v___x_2317_);
lean_dec(v_j_2276_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2318_);
v___x_2320_ = v___x_2292_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2276_);
return v_x_2269_;
}
}
}
else
{
lean_object* v_ks_2327_; lean_object* v_vs_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2342_; 
v_ks_2327_ = lean_ctor_get(v_x_2269_, 0);
v_vs_2328_ = lean_ctor_get(v_x_2269_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2330_ = v_x_2269_;
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_vs_2328_);
lean_inc(v_ks_2327_);
lean_dec(v_x_2269_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2327_, v_x_2271_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2334_; 
if (v_isShared_2331_ == 0)
{
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_ks_2327_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_vs_2328_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v_val_2336_; lean_object* v_keys_x27_2337_; lean_object* v_vals_x27_2338_; lean_object* v___x_2340_; 
v_val_2336_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_n(v_val_2336_, 2);
lean_dec_ref_known(v___x_2332_, 1);
v_keys_x27_2337_ = l_Array_eraseIdx___redArg(v_ks_2327_, v_val_2336_);
v_vals_x27_2338_ = l_Array_eraseIdx___redArg(v_vs_2328_, v_val_2336_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 1, v_vals_x27_2338_);
lean_ctor_set(v___x_2330_, 0, v_keys_x27_2337_);
v___x_2340_ = v___x_2330_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_keys_x27_2337_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_vals_x27_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
size_t v_x_19389__boxed_2346_; lean_object* v_res_2347_; 
v_x_19389__boxed_2346_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2347_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2343_, v_x_19389__boxed_2346_, v_x_2345_);
lean_dec_ref(v_x_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
size_t v___x_2350_; size_t v___x_2351_; size_t v___x_2352_; uint64_t v___x_2353_; size_t v_h_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_ptr_addr(v_x_2349_);
v___x_2351_ = ((size_t)3ULL);
v___x_2352_ = lean_usize_shift_right(v___x_2350_, v___x_2351_);
v___x_2353_ = lean_usize_to_uint64(v___x_2352_);
v_h_2354_ = lean_uint64_to_usize(v___x_2353_);
v___x_2355_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2348_, v_h_2354_, v_x_2349_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2356_, v_x_2357_);
lean_dec_ref(v_x_2357_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
if (lean_obj_tag(v_as_2359_) == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v_head_2373_; lean_object* v_tail_2374_; lean_object* v___x_2375_; 
v_head_2373_ = lean_ctor_get(v_as_2359_, 0);
lean_inc(v_head_2373_);
v_tail_2374_ = lean_ctor_get(v_as_2359_, 1);
lean_inc(v_tail_2374_);
lean_dec_ref_known(v_as_2359_, 2);
v___x_2375_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2373_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref_known(v___x_2375_, 1);
v_as_2359_ = v_tail_2374_;
goto _start;
}
else
{
lean_dec(v_tail_2374_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2390_, lean_object* v_vals_2391_, lean_object* v_i_2392_, lean_object* v_k_2393_){
_start:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_array_get_size(v_keys_2390_);
v___x_2395_ = lean_nat_dec_lt(v_i_2392_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec(v_i_2392_);
v___x_2396_ = lean_box(0);
return v___x_2396_;
}
else
{
lean_object* v_k_x27_2397_; size_t v___x_2398_; size_t v___x_2399_; uint8_t v___x_2400_; 
v_k_x27_2397_ = lean_array_fget_borrowed(v_keys_2390_, v_i_2392_);
v___x_2398_ = lean_ptr_addr(v_k_2393_);
v___x_2399_ = lean_ptr_addr(v_k_x27_2397_);
v___x_2400_ = lean_usize_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_add(v_i_2392_, v___x_2401_);
lean_dec(v_i_2392_);
v_i_2392_ = v___x_2402_;
goto _start;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_array_fget_borrowed(v_vals_2391_, v_i_2392_);
lean_dec(v_i_2392_);
lean_inc(v___x_2404_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2406_, lean_object* v_vals_2407_, lean_object* v_i_2408_, lean_object* v_k_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2406_, v_vals_2407_, v_i_2408_, v_k_2409_);
lean_dec_ref(v_k_2409_);
lean_dec_ref(v_vals_2407_);
lean_dec_ref(v_keys_2406_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2411_, size_t v_x_2412_, lean_object* v_x_2413_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 0)
{
lean_object* v_es_2414_; lean_object* v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v_j_2418_; lean_object* v___x_2419_; 
v_es_2414_ = lean_ctor_get(v_x_2411_, 0);
v___x_2415_ = lean_box(2);
v___x_2416_ = ((size_t)31ULL);
v___x_2417_ = lean_usize_land(v_x_2412_, v___x_2416_);
v_j_2418_ = lean_usize_to_nat(v___x_2417_);
v___x_2419_ = lean_array_get_borrowed(v___x_2415_, v_es_2414_, v_j_2418_);
lean_dec(v_j_2418_);
switch(lean_obj_tag(v___x_2419_))
{
case 0:
{
lean_object* v_key_2420_; lean_object* v_val_2421_; size_t v___x_2422_; size_t v___x_2423_; uint8_t v___x_2424_; 
v_key_2420_ = lean_ctor_get(v___x_2419_, 0);
v_val_2421_ = lean_ctor_get(v___x_2419_, 1);
v___x_2422_ = lean_ptr_addr(v_x_2413_);
v___x_2423_ = lean_ptr_addr(v_key_2420_);
v___x_2424_ = lean_usize_dec_eq(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_box(0);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
lean_inc(v_val_2421_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_val_2421_);
return v___x_2426_;
}
}
case 1:
{
lean_object* v_node_2427_; size_t v___x_2428_; size_t v___x_2429_; 
v_node_2427_ = lean_ctor_get(v___x_2419_, 0);
v___x_2428_ = ((size_t)5ULL);
v___x_2429_ = lean_usize_shift_right(v_x_2412_, v___x_2428_);
v_x_2411_ = v_node_2427_;
v_x_2412_ = v___x_2429_;
goto _start;
}
default: 
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_box(0);
return v___x_2431_;
}
}
}
else
{
lean_object* v_ks_2432_; lean_object* v_vs_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_ks_2432_ = lean_ctor_get(v_x_2411_, 0);
v_vs_2433_ = lean_ctor_get(v_x_2411_, 1);
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2432_, v_vs_2433_, v___x_2434_, v_x_2413_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
size_t v_x_19614__boxed_2439_; lean_object* v_res_2440_; 
v_x_19614__boxed_2439_ = lean_unbox_usize(v_x_2437_);
lean_dec(v_x_2437_);
v_res_2440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2436_, v_x_19614__boxed_2439_, v_x_2438_);
lean_dec_ref(v_x_2438_);
lean_dec_ref(v_x_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; uint64_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2443_ = lean_ptr_addr(v_x_2442_);
v___x_2444_ = ((size_t)3ULL);
v___x_2445_ = lean_usize_shift_right(v___x_2443_, v___x_2444_);
v___x_2446_ = lean_usize_to_uint64(v___x_2445_);
v___x_2447_ = lean_uint64_to_usize(v___x_2446_);
v___x_2448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2441_, v___x_2447_, v_x_2442_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2449_, v_x_2450_);
lean_dec_ref(v_x_2450_);
lean_dec_ref(v_x_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
if (lean_obj_tag(v_as_x27_2452_) == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_b_2453_);
return v___x_2465_;
}
else
{
lean_object* v_head_2466_; lean_object* v_tail_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_toGoalState_2470_; lean_object* v_ematch_2471_; lean_object* v_delayedThmInsts_2472_; lean_object* v___x_2473_; 
v_head_2466_ = lean_ctor_get(v_as_x27_2452_, 0);
v_tail_2467_ = lean_ctor_get(v_as_x27_2452_, 1);
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_st_ref_get(v___y_2454_);
v_toGoalState_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_toGoalState_2470_);
lean_dec(v___x_2469_);
v_ematch_2471_ = lean_ctor_get(v_toGoalState_2470_, 12);
lean_inc_ref(v_ematch_2471_);
lean_dec_ref(v_toGoalState_2470_);
v_delayedThmInsts_2472_ = lean_ctor_get(v_ematch_2471_, 10);
lean_inc_ref(v_delayedThmInsts_2472_);
lean_dec_ref(v_ematch_2471_);
v___x_2473_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2472_, v_head_2466_);
lean_dec_ref(v_delayedThmInsts_2472_);
if (lean_obj_tag(v___x_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v_toGoalState_2476_; lean_object* v_ematch_2477_; lean_object* v_mvarId_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2532_; 
v_val_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_st_ref_take(v___y_2454_);
v_toGoalState_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_ref(v_toGoalState_2476_);
v_ematch_2477_ = lean_ctor_get(v_toGoalState_2476_, 12);
lean_inc_ref(v_ematch_2477_);
v_mvarId_2478_ = lean_ctor_get(v___x_2475_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2475_, 0);
lean_dec(v_unused_2533_);
v___x_2480_ = v___x_2475_;
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_mvarId_2478_);
lean_dec(v___x_2475_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_nextDeclIdx_2482_; lean_object* v_enodeMap_2483_; lean_object* v_exprs_2484_; lean_object* v_parents_2485_; lean_object* v_congrTable_2486_; lean_object* v_appMap_2487_; lean_object* v_indicesFound_2488_; lean_object* v_newFacts_2489_; uint8_t v_inconsistent_2490_; lean_object* v_nextIdx_2491_; lean_object* v_newRawFacts_2492_; lean_object* v_facts_2493_; lean_object* v_extThms_2494_; lean_object* v_inj_2495_; lean_object* v_split_2496_; lean_object* v_clean_2497_; lean_object* v_sstates_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2530_; 
v_nextDeclIdx_2482_ = lean_ctor_get(v_toGoalState_2476_, 0);
v_enodeMap_2483_ = lean_ctor_get(v_toGoalState_2476_, 1);
v_exprs_2484_ = lean_ctor_get(v_toGoalState_2476_, 2);
v_parents_2485_ = lean_ctor_get(v_toGoalState_2476_, 3);
v_congrTable_2486_ = lean_ctor_get(v_toGoalState_2476_, 4);
v_appMap_2487_ = lean_ctor_get(v_toGoalState_2476_, 5);
v_indicesFound_2488_ = lean_ctor_get(v_toGoalState_2476_, 6);
v_newFacts_2489_ = lean_ctor_get(v_toGoalState_2476_, 7);
v_inconsistent_2490_ = lean_ctor_get_uint8(v_toGoalState_2476_, sizeof(void*)*17);
v_nextIdx_2491_ = lean_ctor_get(v_toGoalState_2476_, 8);
v_newRawFacts_2492_ = lean_ctor_get(v_toGoalState_2476_, 9);
v_facts_2493_ = lean_ctor_get(v_toGoalState_2476_, 10);
v_extThms_2494_ = lean_ctor_get(v_toGoalState_2476_, 11);
v_inj_2495_ = lean_ctor_get(v_toGoalState_2476_, 13);
v_split_2496_ = lean_ctor_get(v_toGoalState_2476_, 14);
v_clean_2497_ = lean_ctor_get(v_toGoalState_2476_, 15);
v_sstates_2498_ = lean_ctor_get(v_toGoalState_2476_, 16);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_toGoalState_2476_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_toGoalState_2476_, 12);
lean_dec(v_unused_2531_);
v___x_2500_ = v_toGoalState_2476_;
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_sstates_2498_);
lean_inc(v_clean_2497_);
lean_inc(v_split_2496_);
lean_inc(v_inj_2495_);
lean_inc(v_extThms_2494_);
lean_inc(v_facts_2493_);
lean_inc(v_newRawFacts_2492_);
lean_inc(v_nextIdx_2491_);
lean_inc(v_newFacts_2489_);
lean_inc(v_indicesFound_2488_);
lean_inc(v_appMap_2487_);
lean_inc(v_congrTable_2486_);
lean_inc(v_parents_2485_);
lean_inc(v_exprs_2484_);
lean_inc(v_enodeMap_2483_);
lean_inc(v_nextDeclIdx_2482_);
lean_dec(v_toGoalState_2476_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_thmMap_2502_; lean_object* v_gmt_2503_; lean_object* v_thms_2504_; lean_object* v_newThms_2505_; lean_object* v_numInstances_2506_; lean_object* v_numDelayedInstances_2507_; lean_object* v_num_2508_; lean_object* v_preInstances_2509_; lean_object* v_nextThmIdx_2510_; lean_object* v_matchEqNames_2511_; lean_object* v_delayedThmInsts_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2529_; 
v_thmMap_2502_ = lean_ctor_get(v_ematch_2477_, 0);
v_gmt_2503_ = lean_ctor_get(v_ematch_2477_, 1);
v_thms_2504_ = lean_ctor_get(v_ematch_2477_, 2);
v_newThms_2505_ = lean_ctor_get(v_ematch_2477_, 3);
v_numInstances_2506_ = lean_ctor_get(v_ematch_2477_, 4);
v_numDelayedInstances_2507_ = lean_ctor_get(v_ematch_2477_, 5);
v_num_2508_ = lean_ctor_get(v_ematch_2477_, 6);
v_preInstances_2509_ = lean_ctor_get(v_ematch_2477_, 7);
v_nextThmIdx_2510_ = lean_ctor_get(v_ematch_2477_, 8);
v_matchEqNames_2511_ = lean_ctor_get(v_ematch_2477_, 9);
v_delayedThmInsts_2512_ = lean_ctor_get(v_ematch_2477_, 10);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_ematch_2477_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2514_ = v_ematch_2477_;
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
lean_dec(v_ematch_2477_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2529_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2512_, v_head_2466_);
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
lean_ctor_set(v___x_2500_, 12, v___x_2518_);
v___x_2520_ = v___x_2500_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_nextDeclIdx_2482_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_enodeMap_2483_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_exprs_2484_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_parents_2485_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_congrTable_2486_);
lean_ctor_set(v_reuseFailAlloc_2527_, 5, v_appMap_2487_);
lean_ctor_set(v_reuseFailAlloc_2527_, 6, v_indicesFound_2488_);
lean_ctor_set(v_reuseFailAlloc_2527_, 7, v_newFacts_2489_);
lean_ctor_set(v_reuseFailAlloc_2527_, 8, v_nextIdx_2491_);
lean_ctor_set(v_reuseFailAlloc_2527_, 9, v_newRawFacts_2492_);
lean_ctor_set(v_reuseFailAlloc_2527_, 10, v_facts_2493_);
lean_ctor_set(v_reuseFailAlloc_2527_, 11, v_extThms_2494_);
lean_ctor_set(v_reuseFailAlloc_2527_, 12, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2527_, 13, v_inj_2495_);
lean_ctor_set(v_reuseFailAlloc_2527_, 14, v_split_2496_);
lean_ctor_set(v_reuseFailAlloc_2527_, 15, v_clean_2497_);
lean_ctor_set(v_reuseFailAlloc_2527_, 16, v_sstates_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2527_, sizeof(void*)*17, v_inconsistent_2490_);
v___x_2520_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2520_);
v___x_2522_ = v___x_2480_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_mvarId_2478_);
v___x_2522_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_st_ref_put(v___y_2454_, v___x_2522_);
v___x_2524_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2474_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref_known(v___x_2524_, 1);
v_as_x27_2452_ = v_tail_2467_;
v_b_2453_ = v___x_2468_;
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
lean_dec(v___x_2473_);
v_as_x27_2452_ = v_tail_2467_;
v_b_2453_ = v___x_2468_;
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
v_ematch_2569_ = lean_ctor_get(v_toGoalState_2568_, 12);
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
size_t v_x_19919__boxed_2669_; lean_object* v_res_2670_; 
v_x_19919__boxed_2669_ = lean_unbox_usize(v_x_2667_);
lean_dec(v_x_2667_);
v_res_2670_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2665_, v_x_2666_, v_x_19919__boxed_2669_, v_x_2668_);
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
size_t v_x_19930__boxed_2680_; lean_object* v_res_2681_; 
v_x_19930__boxed_2680_ = lean_unbox_usize(v_x_2678_);
lean_dec(v_x_2678_);
v_res_2681_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2676_, v_x_2677_, v_x_19930__boxed_2680_, v_x_2679_);
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
size_t v_x_25951__boxed_2747_; lean_object* v_res_2748_; 
v_x_25951__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v_x_25951__boxed_2747_, v_x_2746_);
lean_dec_ref(v___x_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
uint64_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
lean_inc_ref(v_x_2751_);
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
lean_inc_n(v_k_2888_, 2);
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
size_t v_x_26105__boxed_2915_; size_t v_x_26106__boxed_2916_; lean_object* v_res_2917_; 
v_x_26105__boxed_2915_ = lean_unbox_usize(v_x_2911_);
lean_dec(v_x_2911_);
v_x_26106__boxed_2916_ = lean_unbox_usize(v_x_2912_);
lean_dec(v_x_2912_);
v_res_2917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2909_, v_x_2910_, v_x_26105__boxed_2915_, v_x_26106__boxed_2916_, v_x_2913_, v_x_2914_);
lean_dec_ref(v___x_2909_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_){
_start:
{
uint64_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
lean_inc_ref(v_x_2920_);
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
lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3116_; 
v_snd_2946_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_3117_);
v___x_2948_ = v_a_2938_;
v_isShared_2949_ = v_isSharedCheck_3116_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_dec(v_a_2938_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3116_;
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
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3107_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3107_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3107_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_self_2957_; lean_object* v_next_2958_; lean_object* v_congr_2959_; lean_object* v_target_x3f_2960_; lean_object* v_proof_x3f_2961_; uint8_t v_flipped_2962_; lean_object* v_size_2963_; uint8_t v_interpreted_2964_; uint8_t v_ctor_2965_; uint8_t v_hasLambdas_2966_; uint8_t v_heqProofs_2967_; lean_object* v_idx_2968_; lean_object* v_generation_2969_; lean_object* v_mt_2970_; lean_object* v_sTerms_2971_; uint8_t v_funCC_2972_; lean_object* v_ematchDiagSource_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3105_; 
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
v_isSharedCheck_3105_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v_a_2953_, 2);
lean_dec(v_unused_3106_);
v___x_2975_ = v_a_2953_;
v_isShared_2976_ = v_isSharedCheck_3105_;
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
v_isShared_2976_ = v_isSharedCheck_3105_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___y_2993_; lean_object* v___x_3003_; 
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
v___x_3003_ = v___x_2975_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_self_2957_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_next_2958_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_rootNew_2936_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_congr_2959_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_target_x3f_2960_);
lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_proof_x3f_2961_);
lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_size_2963_);
lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_idx_2968_);
lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_generation_2969_);
lean_ctor_set(v_reuseFailAlloc_3104_, 9, v_mt_2970_);
lean_ctor_set(v_reuseFailAlloc_3104_, 10, v_sTerms_2971_);
lean_ctor_set(v_reuseFailAlloc_3104_, 11, v_ematchDiagSource_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12, v_flipped_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 1, v_interpreted_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 2, v_ctor_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 3, v_hasLambdas_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 4, v_heqProofs_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 5, v_funCC_2972_);
v___x_3003_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3002_;
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
v___jp_2992_:
{
if (lean_obj_tag(v___y_2993_) == 0)
{
lean_dec_ref_known(v___y_2993_, 1);
goto v___jp_2977_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v_next_2958_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_2994_ = lean_ctor_get(v___y_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___y_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___y_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___y_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v___x_3003_);
lean_inc_ref(v_self_2957_);
v___x_3004_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2957_, v___x_3003_, v___y_2939_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_dec_ref_known(v___x_3004_, 1);
if (v_a_2937_ == 0)
{
lean_dec_ref(v___x_3003_);
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
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3006_ = lean_unsigned_to_nat(3u);
v___x_3007_ = l_Lean_Expr_isAppOfArity(v_self_2957_, v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3003_);
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
uint8_t v___x_3008_; 
v___x_3008_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3003_);
lean_dec_ref(v___x_3003_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v_toGoalState_3010_; lean_object* v_enodeMap_3011_; lean_object* v_congrTable_3012_; lean_object* v___x_3013_; 
v___x_3009_ = lean_st_ref_get(v___y_2939_);
v_toGoalState_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc_ref(v_toGoalState_3010_);
lean_dec(v___x_3009_);
v_enodeMap_3011_ = lean_ctor_get(v_toGoalState_3010_, 1);
lean_inc_ref(v_enodeMap_3011_);
v_congrTable_3012_ = lean_ctor_get(v_toGoalState_3010_, 4);
lean_inc_ref(v_congrTable_3012_);
lean_dec_ref(v_toGoalState_3010_);
lean_inc_ref(v_self_2957_);
v___x_3013_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3011_, v_congrTable_3012_, v_self_2957_);
lean_dec_ref(v_congrTable_3012_);
lean_dec_ref(v_enodeMap_3011_);
if (lean_obj_tag(v___x_3013_) == 0)
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
lean_object* v_val_3014_; lean_object* v_fst_3015_; lean_object* v___x_3016_; 
v_val_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v_fst_3015_ = lean_ctor_get(v_val_3014_, 0);
lean_inc(v_fst_3015_);
lean_dec(v_val_3014_);
v___x_3016_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3015_, v___y_2940_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; uint8_t v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_unbox(v_a_3017_);
lean_dec(v_a_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v_toGoalState_3020_; lean_object* v_mvarId_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3095_; 
v___x_3019_ = lean_st_ref_take(v___y_2939_);
v_toGoalState_3020_ = lean_ctor_get(v___x_3019_, 0);
v_mvarId_3021_ = lean_ctor_get(v___x_3019_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3023_ = v___x_3019_;
v_isShared_3024_ = v_isSharedCheck_3095_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_mvarId_3021_);
lean_inc(v_toGoalState_3020_);
lean_dec(v___x_3019_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3095_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_nextDeclIdx_3025_; lean_object* v_enodeMap_3026_; lean_object* v_exprs_3027_; lean_object* v_parents_3028_; lean_object* v_congrTable_3029_; lean_object* v_appMap_3030_; lean_object* v_indicesFound_3031_; lean_object* v_newFacts_3032_; uint8_t v_inconsistent_3033_; lean_object* v_nextIdx_3034_; lean_object* v_newRawFacts_3035_; lean_object* v_facts_3036_; lean_object* v_extThms_3037_; lean_object* v_ematch_3038_; lean_object* v_inj_3039_; lean_object* v_split_3040_; lean_object* v_clean_3041_; lean_object* v_sstates_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3094_; 
v_nextDeclIdx_3025_ = lean_ctor_get(v_toGoalState_3020_, 0);
v_enodeMap_3026_ = lean_ctor_get(v_toGoalState_3020_, 1);
v_exprs_3027_ = lean_ctor_get(v_toGoalState_3020_, 2);
v_parents_3028_ = lean_ctor_get(v_toGoalState_3020_, 3);
v_congrTable_3029_ = lean_ctor_get(v_toGoalState_3020_, 4);
v_appMap_3030_ = lean_ctor_get(v_toGoalState_3020_, 5);
v_indicesFound_3031_ = lean_ctor_get(v_toGoalState_3020_, 6);
v_newFacts_3032_ = lean_ctor_get(v_toGoalState_3020_, 7);
v_inconsistent_3033_ = lean_ctor_get_uint8(v_toGoalState_3020_, sizeof(void*)*17);
v_nextIdx_3034_ = lean_ctor_get(v_toGoalState_3020_, 8);
v_newRawFacts_3035_ = lean_ctor_get(v_toGoalState_3020_, 9);
v_facts_3036_ = lean_ctor_get(v_toGoalState_3020_, 10);
v_extThms_3037_ = lean_ctor_get(v_toGoalState_3020_, 11);
v_ematch_3038_ = lean_ctor_get(v_toGoalState_3020_, 12);
v_inj_3039_ = lean_ctor_get(v_toGoalState_3020_, 13);
v_split_3040_ = lean_ctor_get(v_toGoalState_3020_, 14);
v_clean_3041_ = lean_ctor_get(v_toGoalState_3020_, 15);
v_sstates_3042_ = lean_ctor_get(v_toGoalState_3020_, 16);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_toGoalState_3020_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3044_ = v_toGoalState_3020_;
v_isShared_3045_ = v_isSharedCheck_3094_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_sstates_3042_);
lean_inc(v_clean_3041_);
lean_inc(v_split_3040_);
lean_inc(v_inj_3039_);
lean_inc(v_ematch_3038_);
lean_inc(v_extThms_3037_);
lean_inc(v_facts_3036_);
lean_inc(v_newRawFacts_3035_);
lean_inc(v_nextIdx_3034_);
lean_inc(v_newFacts_3032_);
lean_inc(v_indicesFound_3031_);
lean_inc(v_appMap_3030_);
lean_inc(v_congrTable_3029_);
lean_inc(v_parents_3028_);
lean_inc(v_exprs_3027_);
lean_inc(v_enodeMap_3026_);
lean_inc(v_nextDeclIdx_3025_);
lean_dec(v_toGoalState_3020_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3094_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_box(0);
lean_inc_ref(v_self_2957_);
v___x_3047_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3026_, v_congrTable_3029_, v_self_2957_, v___x_3046_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 4, v___x_3047_);
v___x_3049_ = v___x_3044_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_nextDeclIdx_3025_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_enodeMap_3026_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_exprs_3027_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_parents_3028_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_appMap_3030_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_indicesFound_3031_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_newFacts_3032_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v_nextIdx_3034_);
lean_ctor_set(v_reuseFailAlloc_3093_, 9, v_newRawFacts_3035_);
lean_ctor_set(v_reuseFailAlloc_3093_, 10, v_facts_3036_);
lean_ctor_set(v_reuseFailAlloc_3093_, 11, v_extThms_3037_);
lean_ctor_set(v_reuseFailAlloc_3093_, 12, v_ematch_3038_);
lean_ctor_set(v_reuseFailAlloc_3093_, 13, v_inj_3039_);
lean_ctor_set(v_reuseFailAlloc_3093_, 14, v_split_3040_);
lean_ctor_set(v_reuseFailAlloc_3093_, 15, v_clean_3041_);
lean_ctor_set(v_reuseFailAlloc_3093_, 16, v_sstates_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3093_, sizeof(void*)*17, v_inconsistent_3033_);
v___x_3049_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3049_);
v___x_3051_ = v___x_3023_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_mvarId_3021_);
v___x_3051_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_put(v___y_2939_, v___x_3051_);
lean_inc_ref(v_rootNew_2936_);
lean_inc_ref(v_next_2958_);
lean_inc_ref_n(v_self_2957_, 3);
v___x_3053_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3053_, 0, v_self_2957_);
lean_ctor_set(v___x_3053_, 1, v_next_2958_);
lean_ctor_set(v___x_3053_, 2, v_rootNew_2936_);
lean_ctor_set(v___x_3053_, 3, v_self_2957_);
lean_ctor_set(v___x_3053_, 4, v_target_x3f_2960_);
lean_ctor_set(v___x_3053_, 5, v_proof_x3f_2961_);
lean_ctor_set(v___x_3053_, 6, v_size_2963_);
lean_ctor_set(v___x_3053_, 7, v_idx_2968_);
lean_ctor_set(v___x_3053_, 8, v_generation_2969_);
lean_ctor_set(v___x_3053_, 9, v_mt_2970_);
lean_ctor_set(v___x_3053_, 10, v_sTerms_2971_);
lean_ctor_set(v___x_3053_, 11, v_ematchDiagSource_2973_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12, v_flipped_2962_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 1, v_interpreted_2964_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 2, v_ctor_2965_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 3, v_hasLambdas_2966_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 4, v_heqProofs_2967_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 5, v_funCC_2972_);
v___x_3054_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2957_, v___x_3053_, v___y_2939_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = lean_st_ref_get(v___y_2939_);
lean_inc(v_fst_3015_);
v___x_3056_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3055_, v_fst_3015_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___x_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v_self_3058_; lean_object* v_next_3059_; lean_object* v_root_3060_; lean_object* v_target_x3f_3061_; lean_object* v_proof_x3f_3062_; uint8_t v_flipped_3063_; lean_object* v_size_3064_; uint8_t v_interpreted_3065_; uint8_t v_ctor_3066_; uint8_t v_hasLambdas_3067_; uint8_t v_heqProofs_3068_; lean_object* v_idx_3069_; lean_object* v_generation_3070_; lean_object* v_mt_3071_; lean_object* v_sTerms_3072_; uint8_t v_funCC_3073_; lean_object* v_ematchDiagSource_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3082_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_self_3058_ = lean_ctor_get(v_a_3057_, 0);
v_next_3059_ = lean_ctor_get(v_a_3057_, 1);
v_root_3060_ = lean_ctor_get(v_a_3057_, 2);
v_target_x3f_3061_ = lean_ctor_get(v_a_3057_, 4);
v_proof_x3f_3062_ = lean_ctor_get(v_a_3057_, 5);
v_flipped_3063_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12);
v_size_3064_ = lean_ctor_get(v_a_3057_, 6);
v_interpreted_3065_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 1);
v_ctor_3066_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 2);
v_hasLambdas_3067_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 3);
v_heqProofs_3068_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 4);
v_idx_3069_ = lean_ctor_get(v_a_3057_, 7);
v_generation_3070_ = lean_ctor_get(v_a_3057_, 8);
v_mt_3071_ = lean_ctor_get(v_a_3057_, 9);
v_sTerms_3072_ = lean_ctor_get(v_a_3057_, 10);
v_funCC_3073_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3074_ = lean_ctor_get(v_a_3057_, 11);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_a_3057_, 3);
lean_dec(v_unused_3083_);
v___x_3076_ = v_a_3057_;
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_ematchDiagSource_3074_);
lean_inc(v_sTerms_3072_);
lean_inc(v_mt_3071_);
lean_inc(v_generation_3070_);
lean_inc(v_idx_3069_);
lean_inc(v_size_3064_);
lean_inc(v_proof_x3f_3062_);
lean_inc(v_target_x3f_3061_);
lean_inc(v_root_3060_);
lean_inc(v_next_3059_);
lean_inc(v_self_3058_);
lean_dec(v_a_3057_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 3, v_self_2957_);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_self_3058_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_next_3059_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_root_3060_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_self_2957_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_target_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3081_, 5, v_proof_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3081_, 6, v_size_3064_);
lean_ctor_set(v_reuseFailAlloc_3081_, 7, v_idx_3069_);
lean_ctor_set(v_reuseFailAlloc_3081_, 8, v_generation_3070_);
lean_ctor_set(v_reuseFailAlloc_3081_, 9, v_mt_3071_);
lean_ctor_set(v_reuseFailAlloc_3081_, 10, v_sTerms_3072_);
lean_ctor_set(v_reuseFailAlloc_3081_, 11, v_ematchDiagSource_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12, v_flipped_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 1, v_interpreted_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 2, v_ctor_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 3, v_hasLambdas_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 4, v_heqProofs_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 5, v_funCC_3073_);
v___x_3079_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3015_, v___x_3079_, v___y_2939_);
v___y_2993_ = v___x_3080_;
goto v___jp_2992_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_fst_3015_);
lean_dec_ref(v_next_2958_);
lean_dec_ref(v_self_2957_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3084_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3056_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3056_);
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
lean_dec(v_fst_3015_);
lean_dec_ref(v_self_2957_);
v___y_2993_ = v___x_3054_;
goto v___jp_2992_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3015_);
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
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_fst_3015_);
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
v_a_3096_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3016_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3016_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
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
lean_dec_ref(v___x_3003_);
lean_dec(v_ematchDiagSource_2973_);
lean_dec(v_sTerms_2971_);
lean_dec(v_mt_2970_);
lean_dec(v_generation_2969_);
lean_dec(v_idx_2968_);
lean_dec(v_size_2963_);
lean_dec(v_proof_x3f_2961_);
lean_dec(v_target_x3f_2960_);
lean_dec_ref(v_self_2957_);
v___y_2993_ = v___x_3004_;
goto v___jp_2992_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_2948_);
lean_dec(v_snd_2946_);
lean_dec_ref(v_rootNew_2936_);
v_a_3108_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_2952_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_2952_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3118_, lean_object* v_rootNew_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_a_26289__boxed_3129_; lean_object* v_res_3130_; 
v_a_26289__boxed_3129_ = lean_unbox(v_a_3120_);
v_res_3130_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3118_, v_rootNew_3119_, v_a_26289__boxed_3129_, v_a_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v_lhs_3118_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3131_, lean_object* v_rootNew_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3132_, v_a_3137_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_box(0);
lean_inc_ref(v_lhs_3131_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v_lhs_3131_);
v___x_3148_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
v___x_3149_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3131_, v_rootNew_3132_, v___x_3148_, v___x_3147_, v_a_3133_, v_a_3137_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec_ref(v_lhs_3131_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3163_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3163_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3163_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_fst_3154_; 
v_fst_3154_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_fst_3154_);
lean_dec(v_a_3150_);
if (lean_obj_tag(v_fst_3154_) == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_box(0);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3155_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3161_; 
v_val_3159_ = lean_ctor_get(v_fst_3154_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v_fst_3154_, 1);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v_val_3159_);
v___x_3161_ = v___x_3152_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_val_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_a_3164_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3149_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3149_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v_rootNew_3132_);
lean_dec_ref(v_lhs_3131_);
v_a_3172_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3144_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3144_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3180_, lean_object* v_rootNew_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3180_, v_rootNew_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3194_, v_x_3196_, v_x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3199_, lean_object* v_00_u03b2_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3199_, v_00_u03b2_3200_, v_x_3201_, v_x_3202_);
lean_dec_ref(v_x_3201_);
lean_dec_ref(v___x_3199_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3204_, lean_object* v_00_u03b2_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3204_, v_x_3206_, v_x_3207_, v_x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3210_, lean_object* v_00_u03b2_3211_, lean_object* v_x_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3210_, v_00_u03b2_3211_, v_x_3212_, v_x_3213_, v_x_3214_);
lean_dec_ref(v___x_3210_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3216_, lean_object* v_rootNew_3217_, uint8_t v_a_3218_, lean_object* v_inst_3219_, lean_object* v_a_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3216_, v_rootNew_3217_, v_a_3218_, v_a_3220_, v___y_3221_, v___y_3225_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3233_, lean_object* v_rootNew_3234_, lean_object* v_a_3235_, lean_object* v_inst_3236_, lean_object* v_a_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_a_26648__boxed_3249_; lean_object* v_res_3250_; 
v_a_26648__boxed_3249_ = lean_unbox(v_a_3235_);
v_res_3250_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3233_, v_rootNew_3234_, v_a_26648__boxed_3249_, v_inst_3236_, v_a_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v_lhs_3233_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3251_, lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, size_t v_x_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v___x_3256_; 
lean_inc_ref(v_x_3253_);
v___x_3256_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3251_, v_x_3253_, v_x_3254_, v_x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3257_, lean_object* v_00_u03b2_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
size_t v_x_26691__boxed_3262_; lean_object* v_res_3263_; 
v_x_26691__boxed_3262_ = lean_unbox_usize(v_x_3260_);
lean_dec(v_x_3260_);
v_res_3263_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3257_, v_00_u03b2_3258_, v_x_3259_, v_x_26691__boxed_3262_, v_x_3261_);
lean_dec_ref(v_x_3259_);
lean_dec_ref(v___x_3257_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, size_t v_x_3267_, size_t v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3264_, v_x_3266_, v_x_3267_, v_x_3268_, v_x_3269_, v_x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
size_t v_x_26705__boxed_3279_; size_t v_x_26706__boxed_3280_; lean_object* v_res_3281_; 
v_x_26705__boxed_3279_ = lean_unbox_usize(v_x_3275_);
lean_dec(v_x_3275_);
v_x_26706__boxed_3280_ = lean_unbox_usize(v_x_3276_);
lean_dec(v_x_3276_);
v_res_3281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3272_, v_00_u03b2_3273_, v_x_3274_, v_x_26705__boxed_3279_, v_x_26706__boxed_3280_, v_x_3277_, v_x_3278_);
lean_dec_ref(v___x_3272_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_keys_3284_, lean_object* v_vals_3285_, lean_object* v_heq_3286_, lean_object* v_i_3287_, lean_object* v_k_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3282_, v_keys_3284_, v_vals_3285_, v_i_3287_, v_k_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3290_, lean_object* v_00_u03b2_3291_, lean_object* v_keys_3292_, lean_object* v_vals_3293_, lean_object* v_heq_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3290_, v_00_u03b2_3291_, v_keys_3292_, v_vals_3293_, v_heq_3294_, v_i_3295_, v_k_3296_);
lean_dec_ref(v_vals_3293_);
lean_dec_ref(v_keys_3292_);
lean_dec_ref(v___x_3290_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_n_3300_, lean_object* v_k_3301_, lean_object* v_v_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3298_, v_n_3300_, v_k_3301_, v_v_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3304_, lean_object* v_00_u03b2_3305_, lean_object* v_n_3306_, lean_object* v_k_3307_, lean_object* v_v_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3304_, v_00_u03b2_3305_, v_n_3306_, v_k_3307_, v_v_3308_);
lean_dec_ref(v___x_3304_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3310_, lean_object* v_00_u03b2_3311_, size_t v_depth_3312_, lean_object* v_keys_3313_, lean_object* v_vals_3314_, lean_object* v_heq_3315_, lean_object* v_i_3316_, lean_object* v_entries_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3310_, v_depth_3312_, v_keys_3313_, v_vals_3314_, v_i_3316_, v_entries_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3319_, lean_object* v_00_u03b2_3320_, lean_object* v_depth_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_entries_3326_){
_start:
{
size_t v_depth_boxed_3327_; lean_object* v_res_3328_; 
v_depth_boxed_3327_ = lean_unbox_usize(v_depth_3321_);
lean_dec(v_depth_3321_);
v_res_3328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3319_, v_00_u03b2_3320_, v_depth_boxed_3327_, v_keys_3322_, v_vals_3323_, v_heq_3324_, v_i_3325_, v_entries_3326_);
lean_dec_ref(v_vals_3323_);
lean_dec_ref(v_keys_3322_);
lean_dec_ref(v___x_3319_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3329_, lean_object* v_00_u03b2_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3329_, v_x_3331_, v_x_3332_, v_x_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3336_, lean_object* v_00_u03b2_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3336_, v_00_u03b2_3337_, v_x_3338_, v_x_3339_, v_x_3340_, v_x_3341_);
lean_dec_ref(v___x_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
if (lean_obj_tag(v_as_x27_3343_) == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_b_3344_);
return v___x_3356_;
}
else
{
lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_head_3357_ = lean_ctor_get(v_as_x27_3343_, 0);
v_tail_3358_ = lean_ctor_get(v_as_x27_3343_, 1);
v___x_3359_ = lean_box(0);
lean_inc(v_head_3357_);
v___x_3360_ = l_Lean_Meta_Grind_propagateUp(v_head_3357_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec_ref_known(v___x_3360_, 1);
v_as_x27_3343_ = v_tail_3358_;
v_b_3344_ = v___x_3359_;
goto _start;
}
else
{
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3362_, lean_object* v_b_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3362_, v_b_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v_as_x27_3362_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
if (lean_obj_tag(v_as_x27_3376_) == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_b_3377_);
return v___x_3389_;
}
else
{
lean_object* v_head_3390_; lean_object* v_tail_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v_head_3390_ = lean_ctor_get(v_as_x27_3376_, 0);
v_tail_3391_ = lean_ctor_get(v_as_x27_3376_, 1);
v___x_3392_ = lean_box(0);
lean_inc(v_head_3390_);
v___x_3393_ = l_Lean_Meta_Grind_propagateDown(v_head_3390_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_dec_ref_known(v___x_3393_, 1);
v_as_x27_3376_ = v_tail_3391_;
v_b_3377_ = v___x_3392_;
goto _start;
}
else
{
return v___x_3393_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3395_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec(v_as_x27_3395_);
return v_res_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_cls_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3413_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3414_ = l_Lean_Name_append(v___x_3413_, v_cls_3412_);
return v___x_3414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3427_, uint8_t v_isHEq_3428_, lean_object* v_lhs_3429_, lean_object* v_rhs_3430_, lean_object* v_lhsNode_3431_, lean_object* v_rhsNode_3432_, lean_object* v_lhsRoot_3433_, lean_object* v_rhsRoot_3434_, uint8_t v_flipped_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; uint8_t v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; uint8_t v___y_3535_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; uint8_t v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3603_; lean_object* v___y_3604_; uint8_t v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_toCold_3685_; lean_object* v_options_3686_; lean_object* v_inheritedTraceOptions_3687_; uint8_t v_hasTrace_3688_; lean_object* v_cls_3689_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v_fns_u2082_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_fns_u2081_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; 
v_toCold_3685_ = lean_ctor_get(v_a_3444_, 0);
v_options_3686_ = lean_ctor_get(v_toCold_3685_, 2);
v_inheritedTraceOptions_3687_ = lean_ctor_get(v_toCold_3685_, 11);
v_hasTrace_3688_ = lean_ctor_get_uint8(v_options_3686_, sizeof(void*)*1);
v_cls_3689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3688_ == 0)
{
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
goto v___jp_3808_;
}
else
{
lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3687_, v_options_3686_, v___x_3889_);
if (v___x_3890_ == 0)
{
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
goto v___jp_3808_;
}
else
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Meta_Grind_updateLastTag(v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v___x_3892_; 
lean_dec_ref_known(v___x_3891_, 1);
lean_inc_ref(v_lhs_3429_);
v___x_3892_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3429_, v_a_3436_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
lean_inc_ref(v_rhs_3430_);
v___x_3894_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3430_, v_a_3436_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
lean_ctor_set(v___x_3897_, 1, v_a_3893_);
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v_a_3895_);
v___x_3901_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3689_, v___x_3900_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_dec_ref_known(v___x_3901_, 1);
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
v___y_3813_ = v_a_3440_;
v___y_3814_ = v_a_3441_;
v___y_3815_ = v_a_3442_;
v___y_3816_ = v_a_3443_;
v___y_3817_ = v_a_3444_;
v___y_3818_ = v_a_3445_;
goto v___jp_3808_;
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3901_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_a_3893_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
v_a_3902_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3894_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3894_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
v_a_3910_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3892_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3892_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3891_;
}
}
}
v___jp_3447_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3454_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3490_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3490_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3490_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_del_object(v___x_3467_);
v___x_3470_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3452_);
lean_dec(v___y_3452_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3470_, v___x_3471_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___x_3470_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; 
lean_dec_ref_known(v___x_3472_, 1);
v___x_3473_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3448_, v___x_3471_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3453_, v___y_3450_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3453_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3474_, 1);
v___x_3475_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3451_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3484_; 
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3475_, 0);
lean_dec(v_unused_3485_);
v___x_3477_ = v___x_3475_;
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v___x_3475_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
uint8_t v___x_3479_; 
v___x_3479_ = l_Lean_Expr_isTrue(v___y_3449_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___y_3448_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3471_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3471_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
else
{
lean_object* v___x_3483_; 
lean_del_object(v___x_3477_);
v___x_3483_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3448_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3448_);
return v___x_3483_;
}
}
}
else
{
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
return v___x_3475_;
}
}
else
{
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
return v___x_3474_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
return v___x_3473_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
return v___x_3472_;
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
v___x_3486_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3486_);
v___x_3488_ = v___x_3467_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
v_a_3491_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3464_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3464_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
v___jp_3499_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc_ref(v___y_3517_);
v___x_3536_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3536_, 0, v___y_3517_);
lean_ctor_set(v___x_3536_, 1, v___y_3526_);
lean_ctor_set(v___x_3536_, 2, v___y_3524_);
lean_ctor_set(v___x_3536_, 3, v___y_3506_);
lean_ctor_set(v___x_3536_, 4, v___y_3534_);
lean_ctor_set(v___x_3536_, 5, v___y_3528_);
lean_ctor_set(v___x_3536_, 6, v___y_3518_);
lean_ctor_set(v___x_3536_, 7, v___y_3513_);
lean_ctor_set(v___x_3536_, 8, v___y_3502_);
lean_ctor_set(v___x_3536_, 9, v___y_3510_);
lean_ctor_set(v___x_3536_, 10, v___y_3521_);
lean_ctor_set(v___x_3536_, 11, v___y_3527_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12, v___y_3523_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 1, v___y_3532_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 2, v___y_3509_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 3, v___y_3522_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 4, v___y_3535_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 5, v___y_3516_);
lean_inc_ref(v___y_3511_);
v___x_3537_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3511_, v___x_3536_, v___y_3529_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3537_, 1);
lean_inc_ref(v___y_3525_);
v___x_3538_ = l_Lean_Meta_Grind_propagateBeta(v___y_3525_, v___y_3531_, v___y_3529_, v___y_3505_, v___y_3500_, v___y_3504_, v___y_3520_, v___y_3519_, v___y_3512_, v___y_3501_, v___y_3530_, v___y_3533_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3539_; 
lean_dec_ref_known(v___x_3538_, 1);
lean_inc_ref(v___y_3508_);
v___x_3539_ = l_Lean_Meta_Grind_propagateBeta(v___y_3508_, v___y_3503_, v___y_3529_, v___y_3505_, v___y_3500_, v___y_3504_, v___y_3520_, v___y_3519_, v___y_3512_, v___y_3501_, v___y_3530_, v___y_3533_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref_known(v___x_3539_, 1);
v___x_3540_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3434_, v_lhsRoot_3433_, v___y_3529_, v___y_3512_, v___y_3501_, v___y_3530_, v___y_3533_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3514_, v___y_3529_);
lean_dec_ref(v___y_3514_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref_known(v___x_3542_, 1);
lean_inc_ref(v___y_3511_);
v___x_3543_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3515_, v___y_3511_, v___y_3529_, v___y_3505_, v___y_3500_, v___y_3504_, v___y_3520_, v___y_3519_, v___y_3512_, v___y_3501_, v___y_3530_, v___y_3533_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3543_, 1);
v___x_3544_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3529_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; uint8_t v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = lean_unbox(v_a_3545_);
lean_dec(v_a_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
v___x_3547_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3517_, v___y_3529_, v___y_3505_, v___y_3500_, v___y_3504_, v___y_3520_, v___y_3519_, v___y_3512_, v___y_3501_, v___y_3530_, v___y_3533_);
lean_dec_ref(v___y_3517_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3448_ = v___y_3507_;
v___y_3449_ = v___y_3511_;
v___y_3450_ = v___y_3508_;
v___y_3451_ = v_a_3541_;
v___y_3452_ = v___y_3515_;
v___y_3453_ = v___y_3525_;
v___y_3454_ = v___y_3529_;
v___y_3455_ = v___y_3505_;
v___y_3456_ = v___y_3500_;
v___y_3457_ = v___y_3504_;
v___y_3458_ = v___y_3520_;
v___y_3459_ = v___y_3519_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3501_;
v___y_3462_ = v___y_3530_;
v___y_3463_ = v___y_3533_;
goto v___jp_3447_;
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
return v___x_3547_;
}
}
else
{
lean_dec_ref(v___y_3517_);
v___y_3448_ = v___y_3507_;
v___y_3449_ = v___y_3511_;
v___y_3450_ = v___y_3508_;
v___y_3451_ = v_a_3541_;
v___y_3452_ = v___y_3515_;
v___y_3453_ = v___y_3525_;
v___y_3454_ = v___y_3529_;
v___y_3455_ = v___y_3505_;
v___y_3456_ = v___y_3500_;
v___y_3457_ = v___y_3504_;
v___y_3458_ = v___y_3520_;
v___y_3459_ = v___y_3519_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3501_;
v___y_3462_ = v___y_3530_;
v___y_3463_ = v___y_3533_;
goto v___jp_3447_;
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
v_a_3548_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3544_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3544_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
return v___x_3543_;
}
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
return v___x_3542_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
v_a_3556_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3540_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3540_);
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
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3539_;
}
}
else
{
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3538_;
}
}
else
{
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3537_;
}
}
v___jp_3564_:
{
if (v_isHEq_3428_ == 0)
{
if (v___y_3578_ == 0)
{
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3570_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3572_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3577_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3574_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3601_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3589_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3596_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3568_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3570_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3572_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3577_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3574_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3601_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3589_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3596_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3578_;
goto v___jp_3499_;
}
}
else
{
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3570_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3572_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3577_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3574_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3601_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3589_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3595_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3596_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3599_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v_isHEq_3428_;
goto v___jp_3499_;
}
}
v___jp_3602_:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3610_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3625_) == 0)
{
uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_dec_ref_known(v___x_3625_, 1);
v___x_3626_ = 0;
v___x_3627_ = lean_st_ref_get(v___y_3615_);
v___x_3628_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3627_, v_lhs_3429_, v___x_3626_);
lean_dec(v___x_3627_);
v___x_3629_ = lean_st_ref_get(v___y_3615_);
lean_inc_ref(v___y_3609_);
v___x_3630_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3629_, v___y_3609_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___x_3629_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_self_3632_; lean_object* v_root_3633_; lean_object* v_congr_3634_; lean_object* v_target_x3f_3635_; lean_object* v_proof_x3f_3636_; uint8_t v_flipped_3637_; lean_object* v_size_3638_; uint8_t v_interpreted_3639_; uint8_t v_ctor_3640_; uint8_t v_hasLambdas_3641_; uint8_t v_heqProofs_3642_; lean_object* v_idx_3643_; lean_object* v_generation_3644_; lean_object* v_mt_3645_; lean_object* v_sTerms_3646_; uint8_t v_funCC_3647_; lean_object* v_ematchDiagSource_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3675_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_self_3632_ = lean_ctor_get(v_a_3631_, 0);
v_root_3633_ = lean_ctor_get(v_a_3631_, 2);
v_congr_3634_ = lean_ctor_get(v_a_3631_, 3);
v_target_x3f_3635_ = lean_ctor_get(v_a_3631_, 4);
v_proof_x3f_3636_ = lean_ctor_get(v_a_3631_, 5);
v_flipped_3637_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12);
v_size_3638_ = lean_ctor_get(v_a_3631_, 6);
v_interpreted_3639_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 1);
v_ctor_3640_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 2);
v_hasLambdas_3641_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 3);
v_heqProofs_3642_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 4);
v_idx_3643_ = lean_ctor_get(v_a_3631_, 7);
v_generation_3644_ = lean_ctor_get(v_a_3631_, 8);
v_mt_3645_ = lean_ctor_get(v_a_3631_, 9);
v_sTerms_3646_ = lean_ctor_get(v_a_3631_, 10);
v_funCC_3647_ = lean_ctor_get_uint8(v_a_3631_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3648_ = lean_ctor_get(v_a_3631_, 11);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_a_3631_, 1);
lean_dec(v_unused_3676_);
v___x_3650_ = v_a_3631_;
v_isShared_3651_ = v_isSharedCheck_3675_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_ematchDiagSource_3648_);
lean_inc(v_sTerms_3646_);
lean_inc(v_mt_3645_);
lean_inc(v_generation_3644_);
lean_inc(v_idx_3643_);
lean_inc(v_size_3638_);
lean_inc(v_proof_x3f_3636_);
lean_inc(v_target_x3f_3635_);
lean_inc(v_congr_3634_);
lean_inc(v_root_3633_);
lean_inc(v_self_3632_);
lean_dec(v_a_3631_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3675_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_self_3652_; lean_object* v_next_3653_; lean_object* v_root_3654_; lean_object* v_congr_3655_; lean_object* v_target_x3f_3656_; lean_object* v_proof_x3f_3657_; uint8_t v_flipped_3658_; lean_object* v_size_3659_; uint8_t v_interpreted_3660_; uint8_t v_ctor_3661_; uint8_t v_hasLambdas_3662_; uint8_t v_heqProofs_3663_; lean_object* v_idx_3664_; lean_object* v_generation_3665_; lean_object* v_mt_3666_; lean_object* v_sTerms_3667_; uint8_t v_funCC_3668_; lean_object* v_ematchDiagSource_3669_; lean_object* v___x_3671_; 
v_self_3652_ = lean_ctor_get(v_rhsRoot_3434_, 0);
v_next_3653_ = lean_ctor_get(v_rhsRoot_3434_, 1);
v_root_3654_ = lean_ctor_get(v_rhsRoot_3434_, 2);
v_congr_3655_ = lean_ctor_get(v_rhsRoot_3434_, 3);
v_target_x3f_3656_ = lean_ctor_get(v_rhsRoot_3434_, 4);
v_proof_x3f_3657_ = lean_ctor_get(v_rhsRoot_3434_, 5);
v_flipped_3658_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12);
v_size_3659_ = lean_ctor_get(v_rhsRoot_3434_, 6);
v_interpreted_3660_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 1);
v_ctor_3661_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 2);
v_hasLambdas_3662_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 3);
v_heqProofs_3663_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 4);
v_idx_3664_ = lean_ctor_get(v_rhsRoot_3434_, 7);
v_generation_3665_ = lean_ctor_get(v_rhsRoot_3434_, 8);
v_mt_3666_ = lean_ctor_get(v_rhsRoot_3434_, 9);
v_sTerms_3667_ = lean_ctor_get(v_rhsRoot_3434_, 10);
v_funCC_3668_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3669_ = lean_ctor_get(v_rhsRoot_3434_, 11);
lean_inc_ref(v_next_3653_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v_next_3653_);
v___x_3671_ = v___x_3650_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_self_3632_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_next_3653_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_root_3633_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_congr_3634_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_target_x3f_3635_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_proof_x3f_3636_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_size_3638_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_idx_3643_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_generation_3644_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_mt_3645_);
lean_ctor_set(v_reuseFailAlloc_3674_, 10, v_sTerms_3646_);
lean_ctor_set(v_reuseFailAlloc_3674_, 11, v_ematchDiagSource_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12, v_flipped_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 1, v_interpreted_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 2, v_ctor_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 3, v_hasLambdas_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 4, v_heqProofs_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 5, v_funCC_3647_);
v___x_3671_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3613_, v___x_3671_, v___y_3615_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3673_; 
lean_dec_ref_known(v___x_3672_, 1);
v___x_3673_ = lean_nat_add(v_size_3659_, v___y_3614_);
lean_dec(v___y_3614_);
if (v_hasLambdas_3662_ == 0)
{
lean_inc(v_target_x3f_3656_);
lean_inc(v_proof_x3f_3657_);
lean_inc(v_ematchDiagSource_3669_);
lean_inc_ref(v_root_3654_);
lean_inc(v_sTerms_3667_);
lean_inc_ref(v_self_3652_);
lean_inc(v_idx_3664_);
lean_inc(v_mt_3666_);
lean_inc_ref(v_congr_3655_);
lean_inc(v_generation_3665_);
v___y_3565_ = v___y_3617_;
v___y_3566_ = v___y_3622_;
v___y_3567_ = v_generation_3665_;
v___y_3568_ = v___y_3607_;
v___y_3569_ = v___y_3618_;
v___y_3570_ = v___y_3608_;
v___y_3571_ = v___y_3616_;
v___y_3572_ = v_congr_3655_;
v___y_3573_ = v___x_3628_;
v___y_3574_ = v___y_3604_;
v___y_3575_ = v_mt_3666_;
v___y_3576_ = v_ctor_3661_;
v___y_3577_ = v___y_3603_;
v___y_3578_ = v_heqProofs_3663_;
v___y_3579_ = v___y_3621_;
v___y_3580_ = v_idx_3664_;
v___y_3581_ = v___y_3609_;
v___y_3582_ = v___y_3610_;
v___y_3583_ = v_funCC_3668_;
v___y_3584_ = v_self_3652_;
v___y_3585_ = v___x_3673_;
v___y_3586_ = v___y_3620_;
v___y_3587_ = v___y_3619_;
v___y_3588_ = v_sTerms_3667_;
v___y_3589_ = v___y_3611_;
v___y_3590_ = v_flipped_3658_;
v___y_3591_ = v_root_3654_;
v___y_3592_ = v___y_3612_;
v___y_3593_ = v_ematchDiagSource_3669_;
v___y_3594_ = v_proof_x3f_3657_;
v___y_3595_ = v___y_3615_;
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___y_3623_;
v___y_3598_ = v_interpreted_3660_;
v___y_3599_ = v___y_3624_;
v___y_3600_ = v_target_x3f_3656_;
v___y_3601_ = v___y_3605_;
goto v___jp_3564_;
}
else
{
lean_inc(v_target_x3f_3656_);
lean_inc(v_proof_x3f_3657_);
lean_inc(v_ematchDiagSource_3669_);
lean_inc_ref(v_root_3654_);
lean_inc(v_sTerms_3667_);
lean_inc_ref(v_self_3652_);
lean_inc(v_idx_3664_);
lean_inc(v_mt_3666_);
lean_inc_ref(v_congr_3655_);
lean_inc(v_generation_3665_);
v___y_3565_ = v___y_3617_;
v___y_3566_ = v___y_3622_;
v___y_3567_ = v_generation_3665_;
v___y_3568_ = v___y_3607_;
v___y_3569_ = v___y_3618_;
v___y_3570_ = v___y_3608_;
v___y_3571_ = v___y_3616_;
v___y_3572_ = v_congr_3655_;
v___y_3573_ = v___x_3628_;
v___y_3574_ = v___y_3604_;
v___y_3575_ = v_mt_3666_;
v___y_3576_ = v_ctor_3661_;
v___y_3577_ = v___y_3603_;
v___y_3578_ = v_heqProofs_3663_;
v___y_3579_ = v___y_3621_;
v___y_3580_ = v_idx_3664_;
v___y_3581_ = v___y_3609_;
v___y_3582_ = v___y_3610_;
v___y_3583_ = v_funCC_3668_;
v___y_3584_ = v_self_3652_;
v___y_3585_ = v___x_3673_;
v___y_3586_ = v___y_3620_;
v___y_3587_ = v___y_3619_;
v___y_3588_ = v_sTerms_3667_;
v___y_3589_ = v___y_3611_;
v___y_3590_ = v_flipped_3658_;
v___y_3591_ = v_root_3654_;
v___y_3592_ = v___y_3612_;
v___y_3593_ = v_ematchDiagSource_3669_;
v___y_3594_ = v_proof_x3f_3657_;
v___y_3595_ = v___y_3615_;
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___y_3623_;
v___y_3598_ = v_interpreted_3660_;
v___y_3599_ = v___y_3624_;
v___y_3600_ = v_target_x3f_3656_;
v___y_3601_ = v_hasLambdas_3662_;
goto v___jp_3564_;
}
}
else
{
lean_dec(v___x_3628_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v___x_3628_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
v_a_3677_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3630_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3630_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3625_;
}
}
v___jp_3690_:
{
lean_object* v_self_3706_; lean_object* v_next_3707_; lean_object* v_size_3708_; uint8_t v_hasLambdas_3709_; uint8_t v_heqProofs_3710_; lean_object* v___x_3711_; 
v_self_3706_ = lean_ctor_get(v_lhsRoot_3433_, 0);
v_next_3707_ = lean_ctor_get(v_lhsRoot_3433_, 1);
v_size_3708_ = lean_ctor_get(v_lhsRoot_3433_, 6);
v_hasLambdas_3709_ = lean_ctor_get_uint8(v_lhsRoot_3433_, sizeof(void*)*12 + 3);
v_heqProofs_3710_ = lean_ctor_get_uint8(v_lhsRoot_3433_, sizeof(void*)*12 + 4);
v___x_3711_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3706_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v_root_3713_; lean_object* v___x_3714_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v_root_3713_ = lean_ctor_get(v_rhsNode_3432_, 2);
lean_inc_ref_n(v_root_3713_, 2);
lean_dec_ref(v_rhsNode_3432_);
lean_inc_ref(v_lhs_3429_);
v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3429_, v_root_3713_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_toCold_3715_; lean_object* v_options_3716_; uint8_t v_hasTrace_3717_; 
lean_dec_ref_known(v___x_3714_, 1);
v_toCold_3715_ = lean_ctor_get(v___y_3704_, 0);
v_options_3716_ = lean_ctor_get(v_toCold_3715_, 2);
v_hasTrace_3717_ = lean_ctor_get_uint8(v_options_3716_, sizeof(void*)*1);
if (v_hasTrace_3717_ == 0)
{
lean_inc(v_size_3708_);
lean_inc_ref(v_next_3707_);
lean_inc_ref(v_self_3706_);
v___y_3603_ = v___y_3691_;
v___y_3604_ = v_root_3713_;
v___y_3605_ = v_hasLambdas_3709_;
v___y_3606_ = v___y_3692_;
v___y_3607_ = v_heqProofs_3710_;
v___y_3608_ = v_fns_u2082_3695_;
v___y_3609_ = v_self_3706_;
v___y_3610_ = v_a_3712_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v_next_3707_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_size_3708_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
goto v___jp_3602_;
}
else
{
lean_object* v_inheritedTraceOptions_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_inheritedTraceOptions_3718_ = lean_ctor_get(v_toCold_3715_, 11);
v___x_3719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3718_, v_options_3716_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_inc(v_size_3708_);
lean_inc_ref(v_next_3707_);
lean_inc_ref(v_self_3706_);
v___y_3603_ = v___y_3691_;
v___y_3604_ = v_root_3713_;
v___y_3605_ = v_hasLambdas_3709_;
v___y_3606_ = v___y_3692_;
v___y_3607_ = v_heqProofs_3710_;
v___y_3608_ = v_fns_u2082_3695_;
v___y_3609_ = v_self_3706_;
v___y_3610_ = v_a_3712_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v_next_3707_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_size_3708_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Meta_Grind_updateLastTag(v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; 
lean_dec_ref_known(v___x_3721_, 1);
lean_inc_ref(v_lhs_3429_);
v___x_3722_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3429_, v___y_3696_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
lean_inc_ref(v_root_3713_);
v___x_3724_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3713_, v___y_3696_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = lean_st_ref_get(v___y_3696_);
lean_inc_ref(v_lhs_3429_);
v___x_3727_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3726_, v_lhs_3429_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___x_3726_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3728_, v___y_3696_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3732_, 0, v_a_3723_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v_a_3725_);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v_a_3730_);
v___x_3737_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3689_, v___x_3736_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_dec_ref_known(v___x_3737_, 1);
lean_inc(v_size_3708_);
lean_inc_ref(v_next_3707_);
lean_inc_ref(v_self_3706_);
v___y_3603_ = v___y_3691_;
v___y_3604_ = v_root_3713_;
v___y_3605_ = v_hasLambdas_3709_;
v___y_3606_ = v___y_3692_;
v___y_3607_ = v_heqProofs_3710_;
v___y_3608_ = v_fns_u2082_3695_;
v___y_3609_ = v_self_3706_;
v___y_3610_ = v_a_3712_;
v___y_3611_ = v___y_3693_;
v___y_3612_ = v_next_3707_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v_size_3708_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
v___y_3619_ = v___y_3700_;
v___y_3620_ = v___y_3701_;
v___y_3621_ = v___y_3702_;
v___y_3622_ = v___y_3703_;
v___y_3623_ = v___y_3704_;
v___y_3624_ = v___y_3705_;
goto v___jp_3602_;
}
else
{
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3737_;
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3738_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3729_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3729_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3746_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3727_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3727_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3754_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3724_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3724_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3762_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3722_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3722_);
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
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3721_;
}
}
}
}
else
{
lean_dec_ref(v_root_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3714_;
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_fns_u2082_3695_);
lean_dec_ref(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3770_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3711_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3711_);
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
v___jp_3778_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3793_ = lean_array_get_size(v___y_3779_);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_nat_dec_eq(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v_self_3796_; lean_object* v___x_3797_; 
v_self_3796_ = lean_ctor_get(v_lhsRoot_3433_, 0);
lean_inc_ref(v_self_3796_);
v___x_3797_ = l_Lean_Meta_Grind_getFnRoots(v_self_3796_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___y_3691_ = v___y_3779_;
v___y_3692_ = v_fns_u2081_3782_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v_fns_u2082_3695_ = v_a_3798_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
v___y_3699_ = v___y_3786_;
v___y_3700_ = v___y_3787_;
v___y_3701_ = v___y_3788_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
goto v___jp_3690_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_fns_u2081_3782_);
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3799_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3797_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3797_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v___x_3807_; 
v___x_3807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3691_ = v___y_3779_;
v___y_3692_ = v_fns_u2081_3782_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v_fns_u2082_3695_ = v___x_3807_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
v___y_3699_ = v___y_3786_;
v___y_3700_ = v___y_3787_;
v___y_3701_ = v___y_3788_;
v___y_3702_ = v___y_3789_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
goto v___jp_3690_;
}
}
v___jp_3808_:
{
lean_object* v___x_3819_; 
lean_inc_ref(v_lhs_3429_);
v___x_3819_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3429_, v___y_3809_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3887_; 
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v___x_3819_, 0);
lean_dec(v_unused_3888_);
v___x_3821_ = v___x_3819_;
v_isShared_3822_ = v_isSharedCheck_3887_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v___x_3819_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3887_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_self_3823_; lean_object* v_next_3824_; lean_object* v_root_3825_; lean_object* v_congr_3826_; lean_object* v_size_3827_; uint8_t v_interpreted_3828_; uint8_t v_ctor_3829_; uint8_t v_hasLambdas_3830_; uint8_t v_heqProofs_3831_; lean_object* v_idx_3832_; lean_object* v_generation_3833_; lean_object* v_mt_3834_; lean_object* v_sTerms_3835_; uint8_t v_funCC_3836_; lean_object* v_ematchDiagSource_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3884_; 
v_self_3823_ = lean_ctor_get(v_lhsNode_3431_, 0);
v_next_3824_ = lean_ctor_get(v_lhsNode_3431_, 1);
v_root_3825_ = lean_ctor_get(v_lhsNode_3431_, 2);
v_congr_3826_ = lean_ctor_get(v_lhsNode_3431_, 3);
v_size_3827_ = lean_ctor_get(v_lhsNode_3431_, 6);
v_interpreted_3828_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 1);
v_ctor_3829_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 2);
v_hasLambdas_3830_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 3);
v_heqProofs_3831_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 4);
v_idx_3832_ = lean_ctor_get(v_lhsNode_3431_, 7);
v_generation_3833_ = lean_ctor_get(v_lhsNode_3431_, 8);
v_mt_3834_ = lean_ctor_get(v_lhsNode_3431_, 9);
v_sTerms_3835_ = lean_ctor_get(v_lhsNode_3431_, 10);
v_funCC_3836_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3837_ = lean_ctor_get(v_lhsNode_3431_, 11);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_lhsNode_3431_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; 
v_unused_3885_ = lean_ctor_get(v_lhsNode_3431_, 5);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_lhsNode_3431_, 4);
lean_dec(v_unused_3886_);
v___x_3839_ = v_lhsNode_3431_;
v_isShared_3840_ = v_isSharedCheck_3884_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_ematchDiagSource_3837_);
lean_inc(v_sTerms_3835_);
lean_inc(v_mt_3834_);
lean_inc(v_generation_3833_);
lean_inc(v_idx_3832_);
lean_inc(v_size_3827_);
lean_inc(v_congr_3826_);
lean_inc(v_root_3825_);
lean_inc(v_next_3824_);
lean_inc(v_self_3823_);
lean_dec(v_lhsNode_3431_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3884_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 1);
lean_ctor_set(v___x_3821_, 0, v_rhs_3430_);
v___x_3842_ = v___x_3821_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_rhs_3430_);
v___x_3842_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_proof_3427_);
lean_inc_ref(v_root_3825_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 5, v___x_3843_);
lean_ctor_set(v___x_3839_, 4, v___x_3842_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_self_3823_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_next_3824_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_root_3825_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_congr_3826_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3882_, 5, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3882_, 6, v_size_3827_);
lean_ctor_set(v_reuseFailAlloc_3882_, 7, v_idx_3832_);
lean_ctor_set(v_reuseFailAlloc_3882_, 8, v_generation_3833_);
lean_ctor_set(v_reuseFailAlloc_3882_, 9, v_mt_3834_);
lean_ctor_set(v_reuseFailAlloc_3882_, 10, v_sTerms_3835_);
lean_ctor_set(v_reuseFailAlloc_3882_, 11, v_ematchDiagSource_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 1, v_interpreted_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 2, v_ctor_3829_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 3, v_hasLambdas_3830_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 4, v_heqProofs_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3882_, sizeof(void*)*12 + 5, v_funCC_3836_);
v___x_3845_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*12, v_flipped_3435_);
lean_inc_ref(v_lhs_3429_);
v___x_3846_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3429_, v___x_3845_, v___y_3809_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref_known(v___x_3846_, 1);
v___x_3847_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3433_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3434_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = lean_array_get_size(v_a_3848_);
v___x_3852_ = lean_unsigned_to_nat(0u);
v___x_3853_ = lean_nat_dec_eq(v___x_3851_, v___x_3852_);
if (v___x_3853_ == 0)
{
lean_object* v_self_3854_; lean_object* v___x_3855_; 
v_self_3854_ = lean_ctor_get(v_rhsRoot_3434_, 0);
lean_inc_ref(v_self_3854_);
v___x_3855_ = l_Lean_Meta_Grind_getFnRoots(v_self_3854_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___y_3779_ = v_a_3850_;
v___y_3780_ = v_a_3848_;
v___y_3781_ = v_root_3825_;
v_fns_u2081_3782_ = v_a_3856_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v_a_3850_);
lean_dec(v_a_3848_);
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3857_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3855_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3855_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_object* v___x_3865_; 
v___x_3865_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3779_ = v_a_3850_;
v___y_3780_ = v_a_3848_;
v___y_3781_ = v_root_3825_;
v_fns_u2081_3782_ = v___x_3865_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
goto v___jp_3778_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3848_);
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3866_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3849_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3849_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3874_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3847_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3847_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_dec_ref(v_root_3825_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
return v___x_3846_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3918_ = _args[0];
lean_object* v_isHEq_3919_ = _args[1];
lean_object* v_lhs_3920_ = _args[2];
lean_object* v_rhs_3921_ = _args[3];
lean_object* v_lhsNode_3922_ = _args[4];
lean_object* v_rhsNode_3923_ = _args[5];
lean_object* v_lhsRoot_3924_ = _args[6];
lean_object* v_rhsRoot_3925_ = _args[7];
lean_object* v_flipped_3926_ = _args[8];
lean_object* v_a_3927_ = _args[9];
lean_object* v_a_3928_ = _args[10];
lean_object* v_a_3929_ = _args[11];
lean_object* v_a_3930_ = _args[12];
lean_object* v_a_3931_ = _args[13];
lean_object* v_a_3932_ = _args[14];
lean_object* v_a_3933_ = _args[15];
lean_object* v_a_3934_ = _args[16];
lean_object* v_a_3935_ = _args[17];
lean_object* v_a_3936_ = _args[18];
lean_object* v_a_3937_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3938_; uint8_t v_flipped_boxed_3939_; lean_object* v_res_3940_; 
v_isHEq_boxed_3938_ = lean_unbox(v_isHEq_3919_);
v_flipped_boxed_3939_ = lean_unbox(v_flipped_3926_);
v_res_3940_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3918_, v_isHEq_boxed_3938_, v_lhs_3920_, v_rhs_3921_, v_lhsNode_3922_, v_rhsNode_3923_, v_lhsRoot_3924_, v_rhsRoot_3925_, v_flipped_boxed_3939_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec(v_a_3927_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3941_, lean_object* v_as_x27_3942_, lean_object* v_b_3943_, lean_object* v_a_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3942_, v_b_3943_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3957_, lean_object* v_as_x27_3958_, lean_object* v_b_3959_, lean_object* v_a_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3957_, v_as_x27_3958_, v_b_3959_, v_a_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec(v_as_x27_3958_);
lean_dec(v_as_3957_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3973_, lean_object* v_as_x27_3974_, lean_object* v_b_3975_, lean_object* v_a_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3974_, v_b_3975_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3989_, lean_object* v_as_x27_3990_, lean_object* v_b_3991_, lean_object* v_a_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3989_, v_as_x27_3990_, v_b_3991_, v_a_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec(v_as_x27_3990_);
lean_dec(v_as_3989_);
return v_res_4004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4007_ = l_Lean_stringToMessageData(v___x_4006_);
return v___x_4007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4013_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4014_ = l_Lean_Name_append(v___x_4013_, v___x_4012_);
return v___x_4014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4017_ = l_Lean_stringToMessageData(v___x_4016_);
return v___x_4017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4020_ = l_Lean_stringToMessageData(v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4021_, lean_object* v_rhs_4022_, lean_object* v_proof_4023_, uint8_t v_isHEq_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_st_ref_get(v_a_4025_);
lean_inc_ref(v_lhs_4021_);
v___x_4040_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4039_, v_lhs_4021_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v___x_4039_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = lean_st_ref_get(v_a_4025_);
lean_inc_ref(v_rhs_4022_);
v___x_4043_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4042_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v___x_4042_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v_root_4045_; lean_object* v_root_4046_; size_t v___x_4047_; size_t v___x_4048_; uint8_t v___x_4049_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v_root_4045_ = lean_ctor_get(v_a_4041_, 2);
v_root_4046_ = lean_ctor_get(v_a_4044_, 2);
v___x_4047_ = lean_ptr_addr(v_root_4045_);
v___x_4048_ = lean_ptr_addr(v_root_4046_);
v___x_4049_ = lean_usize_dec_eq(v___x_4047_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_object* v_toCold_4050_; lean_object* v_options_4051_; lean_object* v_inheritedTraceOptions_4052_; uint8_t v_hasTrace_4053_; uint8_t v___x_4054_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4092_; lean_object* v___y_4093_; uint8_t v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4120_; lean_object* v___y_4121_; uint8_t v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4152_; uint8_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; uint8_t v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; uint8_t v___y_4205_; lean_object* v___y_4206_; lean_object* v_size_4207_; uint8_t v_interpreted_4208_; uint8_t v_ctor_4209_; lean_object* v___y_4210_; uint8_t v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; uint8_t v_ctor_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; uint8_t v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v_valueInconsistency_4242_; uint8_t v_trueEqFalse_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; 
v_toCold_4050_ = lean_ctor_get(v_a_4033_, 0);
v_options_4051_ = lean_ctor_get(v_toCold_4050_, 2);
v_inheritedTraceOptions_4052_ = lean_ctor_get(v_toCold_4050_, 11);
v_hasTrace_4053_ = lean_ctor_get_uint8(v_options_4051_, sizeof(void*)*1);
v___x_4054_ = 1;
if (v_hasTrace_4053_ == 0)
{
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
v___y_4303_ = v_a_4028_;
v___y_4304_ = v_a_4029_;
v___y_4305_ = v_a_4030_;
v___y_4306_ = v_a_4031_;
v___y_4307_ = v_a_4032_;
v___y_4308_ = v_a_4033_;
v___y_4309_ = v_a_4034_;
goto v___jp_4299_;
}
else
{
lean_object* v___x_4343_; lean_object* v_____do__lift_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4359_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4052_, v_options_4051_, v___x_4358_);
if (v___x_4359_ == 0)
{
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
v___y_4303_ = v_a_4028_;
v___y_4304_ = v_a_4029_;
v___y_4305_ = v_a_4030_;
v___y_4306_ = v_a_4031_;
v___y_4307_ = v_a_4032_;
v___y_4308_ = v_a_4033_;
v___y_4309_ = v_a_4034_;
goto v___jp_4299_;
}
else
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_Meta_Grind_updateLastTag(v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_dec_ref_known(v___x_4360_, 1);
if (v_isHEq_4024_ == 0)
{
lean_object* v___x_4361_; 
lean_inc_ref(v_rhs_4022_);
lean_inc_ref(v_lhs_4021_);
v___x_4361_ = l_Lean_Meta_mkEq(v_lhs_4021_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v_____do__lift_4345_ = v_a_4362_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
v___y_4349_ = v_a_4028_;
v___y_4350_ = v_a_4029_;
v___y_4351_ = v_a_4030_;
v___y_4352_ = v_a_4031_;
v___y_4353_ = v_a_4032_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
goto v___jp_4344_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4363_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4361_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v___x_4371_; 
lean_inc_ref(v_rhs_4022_);
lean_inc_ref(v_lhs_4021_);
v___x_4371_ = l_Lean_Meta_mkHEq(v_lhs_4021_, v_rhs_4022_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v_____do__lift_4345_ = v_a_4372_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
v___y_4349_ = v_a_4028_;
v___y_4350_ = v_a_4029_;
v___y_4351_ = v_a_4030_;
v___y_4352_ = v_a_4031_;
v___y_4353_ = v_a_4032_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
goto v___jp_4344_;
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4373_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4371_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
else
{
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4360_;
}
}
v___jp_4344_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = l_Lean_MessageData_ofExpr(v_____do__lift_4345_);
v___x_4357_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4343_, v___x_4356_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_dec_ref_known(v___x_4357_, 1);
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
v___y_4305_ = v___y_4351_;
v___y_4306_ = v___y_4352_;
v___y_4307_ = v___y_4353_;
v___y_4308_ = v___y_4354_;
v___y_4309_ = v___y_4355_;
goto v___jp_4299_;
}
else
{
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4357_;
}
}
}
v___jp_4055_:
{
lean_object* v_toCold_4066_; lean_object* v_options_4067_; uint8_t v_hasTrace_4068_; 
v_toCold_4066_ = lean_ctor_get(v___y_4064_, 0);
v_options_4067_ = lean_ctor_get(v_toCold_4066_, 2);
v_hasTrace_4068_ = lean_ctor_get_uint8(v_options_4067_, sizeof(void*)*1);
if (v_hasTrace_4068_ == 0)
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4069_;
}
else
{
lean_object* v_inheritedTraceOptions_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v_inheritedTraceOptions_4070_ = lean_ctor_get(v_toCold_4066_, 11);
v___x_4071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4070_, v_options_4067_, v___x_4072_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4074_;
}
else
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_Grind_updateLastTag(v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref_known(v___x_4075_, 1);
v___x_4076_ = lean_st_ref_get(v___y_4056_);
v___x_4077_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4076_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___x_4076_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v_a_4078_);
v___x_4081_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4071_, v___x_4080_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v___x_4082_; 
lean_dec_ref_known(v___x_4081_, 1);
v___x_4082_ = l_Lean_Meta_Grind_checkInvariants(v___x_4049_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4082_;
}
else
{
return v___x_4081_;
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
v_a_4083_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4077_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4077_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
return v___x_4075_;
}
}
}
}
v___jp_4091_:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4095_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; uint8_t v___x_4107_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v___x_4107_ = lean_unbox(v_a_4106_);
lean_dec(v_a_4106_);
if (v___x_4107_ == 0)
{
if (v___y_4094_ == 0)
{
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___y_4092_);
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
goto v___jp_4055_;
}
else
{
lean_object* v_self_4108_; lean_object* v_self_4109_; lean_object* v___x_4110_; 
v_self_4108_ = lean_ctor_get(v___y_4093_, 0);
lean_inc_ref(v_self_4108_);
lean_dec_ref(v___y_4093_);
v_self_4109_ = lean_ctor_get(v___y_4092_, 0);
lean_inc_ref(v_self_4109_);
lean_dec_ref(v___y_4092_);
v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4108_, v_self_4109_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_dec_ref_known(v___x_4110_, 1);
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
goto v___jp_4055_;
}
else
{
return v___x_4110_;
}
}
}
else
{
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___y_4092_);
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4100_;
v___y_4062_ = v___y_4101_;
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
goto v___jp_4055_;
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v___y_4093_);
lean_dec_ref(v___y_4092_);
v_a_4111_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4105_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4105_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4119_:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4123_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; uint8_t v___x_4135_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v___x_4133_, 1);
v___x_4135_ = lean_unbox(v_a_4134_);
lean_dec(v_a_4134_);
if (v___x_4135_ == 0)
{
uint8_t v_ctor_4136_; 
v_ctor_4136_ = lean_ctor_get_uint8(v___y_4121_, sizeof(void*)*12 + 2);
if (v_ctor_4136_ == 0)
{
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
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
goto v___jp_4091_;
}
else
{
uint8_t v_ctor_4137_; 
v_ctor_4137_ = lean_ctor_get_uint8(v___y_4120_, sizeof(void*)*12 + 2);
if (v_ctor_4137_ == 0)
{
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
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
goto v___jp_4091_;
}
else
{
lean_object* v_self_4138_; lean_object* v_self_4139_; lean_object* v___x_4140_; 
v_self_4138_ = lean_ctor_get(v___y_4121_, 0);
v_self_4139_ = lean_ctor_get(v___y_4120_, 0);
lean_inc_ref(v_self_4139_);
lean_inc_ref(v_self_4138_);
v___x_4140_ = l_Lean_Meta_Grind_propagateCtor(v_self_4138_, v_self_4139_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref_known(v___x_4140_, 1);
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
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
goto v___jp_4091_;
}
else
{
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v___x_4140_;
}
}
}
}
else
{
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
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
goto v___jp_4091_;
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___y_4121_);
lean_dec_ref(v___y_4120_);
v_a_4141_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4133_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4133_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
v___jp_4149_:
{
if (v___y_4151_ == 0)
{
v___y_4120_ = v___y_4150_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4160_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_dec_ref_known(v___x_4164_, 1);
v___y_4120_ = v___y_4150_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4160_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
goto v___jp_4119_;
}
else
{
lean_dec_ref(v___y_4152_);
lean_dec_ref(v___y_4150_);
return v___x_4164_;
}
}
}
v___jp_4165_:
{
lean_object* v___x_4180_; 
lean_inc_ref(v___y_4168_);
lean_inc_ref(v___y_4174_);
v___x_4180_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4023_, v_isHEq_4024_, v_rhs_4022_, v_lhs_4021_, v_a_4044_, v_a_4041_, v___y_4174_, v___y_4168_, v___x_4054_, v___y_4177_, v___y_4175_, v___y_4167_, v___y_4179_, v___y_4166_, v___y_4170_, v___y_4172_, v___y_4171_, v___y_4169_, v___y_4178_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_dec_ref_known(v___x_4180_, 1);
v___y_4150_ = v___y_4174_;
v___y_4151_ = v___y_4176_;
v___y_4152_ = v___y_4168_;
v___y_4153_ = v___y_4173_;
v___y_4154_ = v___y_4177_;
v___y_4155_ = v___y_4175_;
v___y_4156_ = v___y_4167_;
v___y_4157_ = v___y_4179_;
v___y_4158_ = v___y_4166_;
v___y_4159_ = v___y_4170_;
v___y_4160_ = v___y_4172_;
v___y_4161_ = v___y_4171_;
v___y_4162_ = v___y_4169_;
v___y_4163_ = v___y_4178_;
goto v___jp_4149_;
}
else
{
lean_dec_ref(v___y_4174_);
lean_dec_ref(v___y_4168_);
return v___x_4180_;
}
}
v___jp_4181_:
{
lean_object* v___x_4196_; 
lean_inc_ref(v___y_4190_);
lean_inc_ref(v___y_4184_);
v___x_4196_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4023_, v_isHEq_4024_, v_lhs_4021_, v_rhs_4022_, v_a_4041_, v_a_4044_, v___y_4184_, v___y_4190_, v___x_4049_, v___y_4193_, v___y_4191_, v___y_4183_, v___y_4195_, v___y_4182_, v___y_4186_, v___y_4188_, v___y_4187_, v___y_4185_, v___y_4194_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_dec_ref_known(v___x_4196_, 1);
v___y_4150_ = v___y_4190_;
v___y_4151_ = v___y_4192_;
v___y_4152_ = v___y_4184_;
v___y_4153_ = v___y_4189_;
v___y_4154_ = v___y_4193_;
v___y_4155_ = v___y_4191_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___y_4195_;
v___y_4158_ = v___y_4182_;
v___y_4159_ = v___y_4186_;
v___y_4160_ = v___y_4188_;
v___y_4161_ = v___y_4187_;
v___y_4162_ = v___y_4185_;
v___y_4163_ = v___y_4194_;
goto v___jp_4149_;
}
else
{
lean_dec_ref(v___y_4190_);
lean_dec_ref(v___y_4184_);
return v___x_4196_;
}
}
v___jp_4197_:
{
lean_object* v_size_4215_; uint8_t v___x_4216_; 
v_size_4215_ = lean_ctor_get(v___y_4200_, 6);
v___x_4216_ = lean_nat_dec_lt(v_size_4207_, v_size_4215_);
lean_dec(v_size_4207_);
if (v___x_4216_ == 0)
{
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4199_;
v___y_4184_ = v___y_4200_;
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4210_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
goto v___jp_4181_;
}
else
{
if (v_interpreted_4208_ == 0)
{
if (v_ctor_4209_ == 0)
{
v___y_4166_ = v___y_4198_;
v___y_4167_ = v___y_4199_;
v___y_4168_ = v___y_4200_;
v___y_4169_ = v___y_4201_;
v___y_4170_ = v___y_4202_;
v___y_4171_ = v___y_4203_;
v___y_4172_ = v___y_4204_;
v___y_4173_ = v___y_4205_;
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4210_;
v___y_4176_ = v___y_4211_;
v___y_4177_ = v___y_4212_;
v___y_4178_ = v___y_4213_;
v___y_4179_ = v___y_4214_;
goto v___jp_4165_;
}
else
{
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4199_;
v___y_4184_ = v___y_4200_;
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4210_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
goto v___jp_4181_;
}
}
else
{
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4199_;
v___y_4184_ = v___y_4200_;
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4210_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
goto v___jp_4181_;
}
}
}
v___jp_4217_:
{
if (v_ctor_4221_ == 0)
{
lean_object* v_size_4233_; uint8_t v_interpreted_4234_; uint8_t v_ctor_4235_; 
v_size_4233_ = lean_ctor_get(v___y_4227_, 6);
lean_inc(v_size_4233_);
v_interpreted_4234_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 1);
v_ctor_4235_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 2);
v___y_4198_ = v___y_4218_;
v___y_4199_ = v___y_4219_;
v___y_4200_ = v___y_4220_;
v___y_4201_ = v___y_4222_;
v___y_4202_ = v___y_4223_;
v___y_4203_ = v___y_4224_;
v___y_4204_ = v___y_4225_;
v___y_4205_ = v___y_4226_;
v___y_4206_ = v___y_4227_;
v_size_4207_ = v_size_4233_;
v_interpreted_4208_ = v_interpreted_4234_;
v_ctor_4209_ = v_ctor_4235_;
v___y_4210_ = v___y_4228_;
v___y_4211_ = v___y_4229_;
v___y_4212_ = v___y_4230_;
v___y_4213_ = v___y_4231_;
v___y_4214_ = v___y_4232_;
goto v___jp_4197_;
}
else
{
uint8_t v_ctor_4236_; 
v_ctor_4236_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 2);
if (v_ctor_4236_ == 0)
{
v___y_4166_ = v___y_4218_;
v___y_4167_ = v___y_4219_;
v___y_4168_ = v___y_4220_;
v___y_4169_ = v___y_4222_;
v___y_4170_ = v___y_4223_;
v___y_4171_ = v___y_4224_;
v___y_4172_ = v___y_4225_;
v___y_4173_ = v___y_4226_;
v___y_4174_ = v___y_4227_;
v___y_4175_ = v___y_4228_;
v___y_4176_ = v___y_4229_;
v___y_4177_ = v___y_4230_;
v___y_4178_ = v___y_4231_;
v___y_4179_ = v___y_4232_;
goto v___jp_4165_;
}
else
{
lean_object* v_size_4237_; uint8_t v_interpreted_4238_; 
v_size_4237_ = lean_ctor_get(v___y_4227_, 6);
lean_inc(v_size_4237_);
v_interpreted_4238_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 1);
v___y_4198_ = v___y_4218_;
v___y_4199_ = v___y_4219_;
v___y_4200_ = v___y_4220_;
v___y_4201_ = v___y_4222_;
v___y_4202_ = v___y_4223_;
v___y_4203_ = v___y_4224_;
v___y_4204_ = v___y_4225_;
v___y_4205_ = v___y_4226_;
v___y_4206_ = v___y_4227_;
v_size_4207_ = v_size_4237_;
v_interpreted_4208_ = v_interpreted_4238_;
v_ctor_4209_ = v_ctor_4236_;
v___y_4210_ = v___y_4228_;
v___y_4211_ = v___y_4229_;
v___y_4212_ = v___y_4230_;
v___y_4213_ = v___y_4231_;
v___y_4214_ = v___y_4232_;
goto v___jp_4197_;
}
}
}
v___jp_4239_:
{
uint8_t v_interpreted_4254_; 
v_interpreted_4254_ = lean_ctor_get_uint8(v___y_4241_, sizeof(void*)*12 + 1);
if (v_interpreted_4254_ == 0)
{
uint8_t v_ctor_4255_; 
v_ctor_4255_ = lean_ctor_get_uint8(v___y_4241_, sizeof(void*)*12 + 2);
v___y_4218_ = v___y_4248_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4241_;
v_ctor_4221_ = v_ctor_4255_;
v___y_4222_ = v___y_4252_;
v___y_4223_ = v___y_4249_;
v___y_4224_ = v___y_4251_;
v___y_4225_ = v___y_4250_;
v___y_4226_ = v_valueInconsistency_4242_;
v___y_4227_ = v___y_4240_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v_trueEqFalse_4243_;
v___y_4230_ = v___y_4244_;
v___y_4231_ = v___y_4253_;
v___y_4232_ = v___y_4247_;
goto v___jp_4217_;
}
else
{
uint8_t v_interpreted_4256_; 
v_interpreted_4256_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 1);
if (v_interpreted_4256_ == 0)
{
v___y_4166_ = v___y_4248_;
v___y_4167_ = v___y_4246_;
v___y_4168_ = v___y_4241_;
v___y_4169_ = v___y_4252_;
v___y_4170_ = v___y_4249_;
v___y_4171_ = v___y_4251_;
v___y_4172_ = v___y_4250_;
v___y_4173_ = v_valueInconsistency_4242_;
v___y_4174_ = v___y_4240_;
v___y_4175_ = v___y_4245_;
v___y_4176_ = v_trueEqFalse_4243_;
v___y_4177_ = v___y_4244_;
v___y_4178_ = v___y_4253_;
v___y_4179_ = v___y_4247_;
goto v___jp_4165_;
}
else
{
uint8_t v_ctor_4257_; 
v_ctor_4257_ = lean_ctor_get_uint8(v___y_4241_, sizeof(void*)*12 + 2);
v___y_4218_ = v___y_4248_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4241_;
v_ctor_4221_ = v_ctor_4257_;
v___y_4222_ = v___y_4252_;
v___y_4223_ = v___y_4249_;
v___y_4224_ = v___y_4251_;
v___y_4225_ = v___y_4250_;
v___y_4226_ = v_valueInconsistency_4242_;
v___y_4227_ = v___y_4240_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v_trueEqFalse_4243_;
v___y_4230_ = v___y_4244_;
v___y_4231_ = v___y_4253_;
v___y_4232_ = v___y_4247_;
goto v___jp_4217_;
}
}
}
v___jp_4258_:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4268_, v___y_4270_, v___y_4263_, v___y_4264_, v___y_4266_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_dec_ref_known(v___x_4271_, 1);
v___y_4240_ = v___y_4269_;
v___y_4241_ = v___y_4260_;
v_valueInconsistency_4242_ = v___x_4049_;
v_trueEqFalse_4243_ = v___x_4054_;
v___y_4244_ = v___y_4268_;
v___y_4245_ = v___y_4265_;
v___y_4246_ = v___y_4259_;
v___y_4247_ = v___y_4261_;
v___y_4248_ = v___y_4267_;
v___y_4249_ = v___y_4262_;
v___y_4250_ = v___y_4270_;
v___y_4251_ = v___y_4263_;
v___y_4252_ = v___y_4264_;
v___y_4253_ = v___y_4266_;
goto v___jp_4239_;
}
else
{
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4260_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4271_;
}
}
v___jp_4272_:
{
if (v___y_4277_ == 0)
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_Meta_Grind_hasSameType(v___y_4287_, v___y_4281_, v___y_4286_, v___y_4278_, v___y_4279_, v___y_4282_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; uint8_t v___x_4290_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = lean_unbox(v_a_4289_);
lean_dec(v_a_4289_);
if (v___x_4290_ == 0)
{
v___y_4240_ = v___y_4284_;
v___y_4241_ = v___y_4274_;
v_valueInconsistency_4242_ = v___x_4049_;
v_trueEqFalse_4243_ = v___x_4049_;
v___y_4244_ = v___y_4285_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4273_;
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4283_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4278_;
v___y_4252_ = v___y_4279_;
v___y_4253_ = v___y_4282_;
goto v___jp_4239_;
}
else
{
v___y_4240_ = v___y_4284_;
v___y_4241_ = v___y_4274_;
v_valueInconsistency_4242_ = v___x_4054_;
v_trueEqFalse_4243_ = v___x_4049_;
v___y_4244_ = v___y_4285_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4273_;
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4283_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4278_;
v___y_4252_ = v___y_4279_;
v___y_4253_ = v___y_4282_;
goto v___jp_4239_;
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec_ref(v___y_4284_);
lean_dec_ref(v___y_4274_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4291_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4288_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4288_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4281_);
v___y_4240_ = v___y_4284_;
v___y_4241_ = v___y_4274_;
v_valueInconsistency_4242_ = v___x_4054_;
v_trueEqFalse_4243_ = v___x_4049_;
v___y_4244_ = v___y_4285_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4273_;
v___y_4247_ = v___y_4276_;
v___y_4248_ = v___y_4283_;
v___y_4249_ = v___y_4275_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4278_;
v___y_4252_ = v___y_4279_;
v___y_4253_ = v___y_4282_;
goto v___jp_4239_;
}
}
v___jp_4299_:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_st_ref_get(v___y_4300_);
lean_inc_ref(v_root_4045_);
v___x_4311_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4310_, v_root_4045_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___x_4310_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = lean_st_ref_get(v___y_4300_);
lean_inc_ref(v_root_4046_);
v___x_4314_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4313_, v_root_4046_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___x_4313_);
if (lean_obj_tag(v___x_4314_) == 0)
{
uint8_t v_interpreted_4315_; 
v_interpreted_4315_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 1);
if (v_interpreted_4315_ == 0)
{
lean_object* v_a_4316_; uint8_t v_ctor_4317_; 
v_a_4316_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4314_, 1);
v_ctor_4317_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 2);
v___y_4218_ = v___y_4304_;
v___y_4219_ = v___y_4302_;
v___y_4220_ = v_a_4312_;
v_ctor_4221_ = v_ctor_4317_;
v___y_4222_ = v___y_4308_;
v___y_4223_ = v___y_4305_;
v___y_4224_ = v___y_4307_;
v___y_4225_ = v___y_4306_;
v___y_4226_ = v___x_4049_;
v___y_4227_ = v_a_4316_;
v___y_4228_ = v___y_4301_;
v___y_4229_ = v___x_4049_;
v___y_4230_ = v___y_4300_;
v___y_4231_ = v___y_4309_;
v___y_4232_ = v___y_4303_;
goto v___jp_4217_;
}
else
{
lean_object* v_a_4318_; uint8_t v_interpreted_4319_; 
v_a_4318_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4314_, 1);
v_interpreted_4319_ = lean_ctor_get_uint8(v_a_4318_, sizeof(void*)*12 + 1);
if (v_interpreted_4319_ == 0)
{
v___y_4166_ = v___y_4304_;
v___y_4167_ = v___y_4302_;
v___y_4168_ = v_a_4312_;
v___y_4169_ = v___y_4308_;
v___y_4170_ = v___y_4305_;
v___y_4171_ = v___y_4307_;
v___y_4172_ = v___y_4306_;
v___y_4173_ = v___x_4049_;
v___y_4174_ = v_a_4318_;
v___y_4175_ = v___y_4301_;
v___y_4176_ = v___x_4049_;
v___y_4177_ = v___y_4300_;
v___y_4178_ = v___y_4309_;
v___y_4179_ = v___y_4303_;
goto v___jp_4165_;
}
else
{
lean_object* v_self_4320_; uint8_t v_ctor_4321_; uint8_t v_heqProofs_4322_; lean_object* v_self_4323_; uint8_t v_heqProofs_4324_; uint8_t v___x_4325_; 
v_self_4320_ = lean_ctor_get(v_a_4312_, 0);
v_ctor_4321_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 2);
v_heqProofs_4322_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 4);
v_self_4323_ = lean_ctor_get(v_a_4318_, 0);
v_heqProofs_4324_ = lean_ctor_get_uint8(v_a_4318_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4045_);
v___x_4325_ = l_Lean_Expr_isTrue(v_root_4045_);
if (v___x_4325_ == 0)
{
uint8_t v___x_4326_; 
lean_inc_ref(v_root_4046_);
v___x_4326_ = l_Lean_Expr_isTrue(v_root_4046_);
if (v___x_4326_ == 0)
{
if (v_isHEq_4024_ == 0)
{
if (v_heqProofs_4322_ == 0)
{
if (v_heqProofs_4324_ == 0)
{
v___y_4218_ = v___y_4304_;
v___y_4219_ = v___y_4302_;
v___y_4220_ = v_a_4312_;
v_ctor_4221_ = v_ctor_4321_;
v___y_4222_ = v___y_4308_;
v___y_4223_ = v___y_4305_;
v___y_4224_ = v___y_4307_;
v___y_4225_ = v___y_4306_;
v___y_4226_ = v___x_4054_;
v___y_4227_ = v_a_4318_;
v___y_4228_ = v___y_4301_;
v___y_4229_ = v___x_4049_;
v___y_4230_ = v___y_4300_;
v___y_4231_ = v___y_4309_;
v___y_4232_ = v___y_4303_;
goto v___jp_4217_;
}
else
{
lean_inc_ref(v_self_4323_);
lean_inc_ref(v_self_4320_);
v___y_4273_ = v___y_4302_;
v___y_4274_ = v_a_4312_;
v___y_4275_ = v___y_4305_;
v___y_4276_ = v___y_4303_;
v___y_4277_ = v___x_4326_;
v___y_4278_ = v___y_4307_;
v___y_4279_ = v___y_4308_;
v___y_4280_ = v___y_4301_;
v___y_4281_ = v_self_4323_;
v___y_4282_ = v___y_4309_;
v___y_4283_ = v___y_4304_;
v___y_4284_ = v_a_4318_;
v___y_4285_ = v___y_4300_;
v___y_4286_ = v___y_4306_;
v___y_4287_ = v_self_4320_;
goto v___jp_4272_;
}
}
else
{
lean_inc_ref(v_self_4323_);
lean_inc_ref(v_self_4320_);
v___y_4273_ = v___y_4302_;
v___y_4274_ = v_a_4312_;
v___y_4275_ = v___y_4305_;
v___y_4276_ = v___y_4303_;
v___y_4277_ = v___x_4326_;
v___y_4278_ = v___y_4307_;
v___y_4279_ = v___y_4308_;
v___y_4280_ = v___y_4301_;
v___y_4281_ = v_self_4323_;
v___y_4282_ = v___y_4309_;
v___y_4283_ = v___y_4304_;
v___y_4284_ = v_a_4318_;
v___y_4285_ = v___y_4300_;
v___y_4286_ = v___y_4306_;
v___y_4287_ = v_self_4320_;
goto v___jp_4272_;
}
}
else
{
lean_inc_ref(v_self_4323_);
lean_inc_ref(v_self_4320_);
v___y_4273_ = v___y_4302_;
v___y_4274_ = v_a_4312_;
v___y_4275_ = v___y_4305_;
v___y_4276_ = v___y_4303_;
v___y_4277_ = v___x_4326_;
v___y_4278_ = v___y_4307_;
v___y_4279_ = v___y_4308_;
v___y_4280_ = v___y_4301_;
v___y_4281_ = v_self_4323_;
v___y_4282_ = v___y_4309_;
v___y_4283_ = v___y_4304_;
v___y_4284_ = v_a_4318_;
v___y_4285_ = v___y_4300_;
v___y_4286_ = v___y_4306_;
v___y_4287_ = v_self_4320_;
goto v___jp_4272_;
}
}
else
{
v___y_4259_ = v___y_4302_;
v___y_4260_ = v_a_4312_;
v___y_4261_ = v___y_4303_;
v___y_4262_ = v___y_4305_;
v___y_4263_ = v___y_4307_;
v___y_4264_ = v___y_4308_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4309_;
v___y_4267_ = v___y_4304_;
v___y_4268_ = v___y_4300_;
v___y_4269_ = v_a_4318_;
v___y_4270_ = v___y_4306_;
goto v___jp_4258_;
}
}
else
{
v___y_4259_ = v___y_4302_;
v___y_4260_ = v_a_4312_;
v___y_4261_ = v___y_4303_;
v___y_4262_ = v___y_4305_;
v___y_4263_ = v___y_4307_;
v___y_4264_ = v___y_4308_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4309_;
v___y_4267_ = v___y_4304_;
v___y_4268_ = v___y_4300_;
v___y_4269_ = v_a_4318_;
v___y_4270_ = v___y_4306_;
goto v___jp_4258_;
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_a_4312_);
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4327_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4314_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4314_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4335_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4311_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4311_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
}
else
{
lean_object* v_toCold_4381_; lean_object* v_options_4382_; uint8_t v_hasTrace_4383_; 
lean_dec(v_a_4044_);
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
v_toCold_4381_ = lean_ctor_get(v_a_4033_, 0);
v_options_4382_ = lean_ctor_get(v_toCold_4381_, 2);
v_hasTrace_4383_ = lean_ctor_get_uint8(v_options_4382_, sizeof(void*)*1);
if (v_hasTrace_4383_ == 0)
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
goto v___jp_4036_;
}
else
{
lean_object* v_inheritedTraceOptions_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_inheritedTraceOptions_4384_ = lean_ctor_get(v_toCold_4381_, 11);
v___x_4385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4384_, v_options_4382_, v___x_4386_);
if (v___x_4387_ == 0)
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
goto v___jp_4036_;
}
else
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Meta_Grind_updateLastTag(v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v___x_4389_; 
lean_dec_ref_known(v___x_4388_, 1);
v___x_4389_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4021_, v_a_4025_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4391_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref_known(v___x_4389_, 1);
v___x_4391_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4022_, v_a_4025_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4394_, 0, v_a_4390_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v_a_4392_);
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4385_, v___x_4397_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_dec_ref_known(v___x_4398_, 1);
goto v___jp_4036_;
}
else
{
return v___x_4398_;
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4390_);
v_a_4399_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4391_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4391_);
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
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec_ref(v_rhs_4022_);
v_a_4407_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4389_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4389_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
return v___x_4388_;
}
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_a_4041_);
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4415_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4043_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4043_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec_ref(v_proof_4023_);
lean_dec_ref(v_rhs_4022_);
lean_dec_ref(v_lhs_4021_);
v_a_4423_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4040_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4040_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
v___jp_4036_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4431_, lean_object* v_rhs_4432_, lean_object* v_proof_4433_, lean_object* v_isHEq_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_){
_start:
{
uint8_t v_isHEq_boxed_4446_; lean_object* v_res_4447_; 
v_isHEq_boxed_4446_ = lean_unbox(v_isHEq_4434_);
v_res_4447_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4431_, v_rhs_4432_, v_proof_4433_, v_isHEq_boxed_4446_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
lean_dec(v_a_4436_);
lean_dec(v_a_4435_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4450_){
_start:
{
lean_object* v___x_4452_; lean_object* v_toGoalState_4453_; lean_object* v_mvarId_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4490_; 
v___x_4452_ = lean_st_ref_take(v_a_4450_);
v_toGoalState_4453_ = lean_ctor_get(v___x_4452_, 0);
v_mvarId_4454_ = lean_ctor_get(v___x_4452_, 1);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4456_ = v___x_4452_;
v_isShared_4457_ = v_isSharedCheck_4490_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_mvarId_4454_);
lean_inc(v_toGoalState_4453_);
lean_dec(v___x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4490_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v_nextDeclIdx_4458_; lean_object* v_enodeMap_4459_; lean_object* v_exprs_4460_; lean_object* v_parents_4461_; lean_object* v_congrTable_4462_; lean_object* v_appMap_4463_; lean_object* v_indicesFound_4464_; uint8_t v_inconsistent_4465_; lean_object* v_nextIdx_4466_; lean_object* v_newRawFacts_4467_; lean_object* v_facts_4468_; lean_object* v_extThms_4469_; lean_object* v_ematch_4470_; lean_object* v_inj_4471_; lean_object* v_split_4472_; lean_object* v_clean_4473_; lean_object* v_sstates_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4488_; 
v_nextDeclIdx_4458_ = lean_ctor_get(v_toGoalState_4453_, 0);
v_enodeMap_4459_ = lean_ctor_get(v_toGoalState_4453_, 1);
v_exprs_4460_ = lean_ctor_get(v_toGoalState_4453_, 2);
v_parents_4461_ = lean_ctor_get(v_toGoalState_4453_, 3);
v_congrTable_4462_ = lean_ctor_get(v_toGoalState_4453_, 4);
v_appMap_4463_ = lean_ctor_get(v_toGoalState_4453_, 5);
v_indicesFound_4464_ = lean_ctor_get(v_toGoalState_4453_, 6);
v_inconsistent_4465_ = lean_ctor_get_uint8(v_toGoalState_4453_, sizeof(void*)*17);
v_nextIdx_4466_ = lean_ctor_get(v_toGoalState_4453_, 8);
v_newRawFacts_4467_ = lean_ctor_get(v_toGoalState_4453_, 9);
v_facts_4468_ = lean_ctor_get(v_toGoalState_4453_, 10);
v_extThms_4469_ = lean_ctor_get(v_toGoalState_4453_, 11);
v_ematch_4470_ = lean_ctor_get(v_toGoalState_4453_, 12);
v_inj_4471_ = lean_ctor_get(v_toGoalState_4453_, 13);
v_split_4472_ = lean_ctor_get(v_toGoalState_4453_, 14);
v_clean_4473_ = lean_ctor_get(v_toGoalState_4453_, 15);
v_sstates_4474_ = lean_ctor_get(v_toGoalState_4453_, 16);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_toGoalState_4453_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v_toGoalState_4453_, 7);
lean_dec(v_unused_4489_);
v___x_4476_ = v_toGoalState_4453_;
v_isShared_4477_ = v_isSharedCheck_4488_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_sstates_4474_);
lean_inc(v_clean_4473_);
lean_inc(v_split_4472_);
lean_inc(v_inj_4471_);
lean_inc(v_ematch_4470_);
lean_inc(v_extThms_4469_);
lean_inc(v_facts_4468_);
lean_inc(v_newRawFacts_4467_);
lean_inc(v_nextIdx_4466_);
lean_inc(v_indicesFound_4464_);
lean_inc(v_appMap_4463_);
lean_inc(v_congrTable_4462_);
lean_inc(v_parents_4461_);
lean_inc(v_exprs_4460_);
lean_inc(v_enodeMap_4459_);
lean_inc(v_nextDeclIdx_4458_);
lean_dec(v_toGoalState_4453_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4488_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4481_; 
v___x_4478_ = lean_box(0);
v___x_4479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 7, v___x_4479_);
v___x_4481_ = v___x_4476_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_nextDeclIdx_4458_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_enodeMap_4459_);
lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_exprs_4460_);
lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_parents_4461_);
lean_ctor_set(v_reuseFailAlloc_4487_, 4, v_congrTable_4462_);
lean_ctor_set(v_reuseFailAlloc_4487_, 5, v_appMap_4463_);
lean_ctor_set(v_reuseFailAlloc_4487_, 6, v_indicesFound_4464_);
lean_ctor_set(v_reuseFailAlloc_4487_, 7, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4487_, 8, v_nextIdx_4466_);
lean_ctor_set(v_reuseFailAlloc_4487_, 9, v_newRawFacts_4467_);
lean_ctor_set(v_reuseFailAlloc_4487_, 10, v_facts_4468_);
lean_ctor_set(v_reuseFailAlloc_4487_, 11, v_extThms_4469_);
lean_ctor_set(v_reuseFailAlloc_4487_, 12, v_ematch_4470_);
lean_ctor_set(v_reuseFailAlloc_4487_, 13, v_inj_4471_);
lean_ctor_set(v_reuseFailAlloc_4487_, 14, v_split_4472_);
lean_ctor_set(v_reuseFailAlloc_4487_, 15, v_clean_4473_);
lean_ctor_set(v_reuseFailAlloc_4487_, 16, v_sstates_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4487_, sizeof(void*)*17, v_inconsistent_4465_);
v___x_4481_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4483_; 
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 0, v___x_4481_);
v___x_4483_ = v___x_4456_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v_mvarId_4454_);
v___x_4483_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = lean_st_ref_put(v_a_4450_, v___x_4483_);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4478_);
return v___x_4485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4491_);
lean_dec(v_a_4491_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4494_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec(v_a_4506_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; lean_object* v_toGoalState_4521_; lean_object* v_newFacts_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4520_ = lean_st_ref_get(v_a_4518_);
v_toGoalState_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc_ref(v_toGoalState_4521_);
lean_dec(v___x_4520_);
v_newFacts_4522_ = lean_ctor_get(v_toGoalState_4521_, 7);
lean_inc_ref(v_newFacts_4522_);
lean_dec_ref(v_toGoalState_4521_);
v___x_4523_ = lean_array_get_size(v_newFacts_4522_);
v___x_4524_ = lean_unsigned_to_nat(1u);
v___x_4525_ = lean_nat_sub(v___x_4523_, v___x_4524_);
v___x_4526_ = lean_nat_dec_lt(v___x_4525_, v___x_4523_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_dec(v___x_4525_);
lean_dec_ref(v_newFacts_4522_);
v___x_4527_ = lean_box(0);
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v_toGoalState_4532_; lean_object* v_mvarId_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4568_; 
v___x_4529_ = lean_array_fget(v_newFacts_4522_, v___x_4525_);
lean_dec(v___x_4525_);
lean_dec_ref(v_newFacts_4522_);
v___x_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
v___x_4531_ = lean_st_ref_take(v_a_4518_);
v_toGoalState_4532_ = lean_ctor_get(v___x_4531_, 0);
v_mvarId_4533_ = lean_ctor_get(v___x_4531_, 1);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4535_ = v___x_4531_;
v_isShared_4536_ = v_isSharedCheck_4568_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_mvarId_4533_);
lean_inc(v_toGoalState_4532_);
lean_dec(v___x_4531_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4568_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v_nextDeclIdx_4537_; lean_object* v_enodeMap_4538_; lean_object* v_exprs_4539_; lean_object* v_parents_4540_; lean_object* v_congrTable_4541_; lean_object* v_appMap_4542_; lean_object* v_indicesFound_4543_; lean_object* v_newFacts_4544_; uint8_t v_inconsistent_4545_; lean_object* v_nextIdx_4546_; lean_object* v_newRawFacts_4547_; lean_object* v_facts_4548_; lean_object* v_extThms_4549_; lean_object* v_ematch_4550_; lean_object* v_inj_4551_; lean_object* v_split_4552_; lean_object* v_clean_4553_; lean_object* v_sstates_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4567_; 
v_nextDeclIdx_4537_ = lean_ctor_get(v_toGoalState_4532_, 0);
v_enodeMap_4538_ = lean_ctor_get(v_toGoalState_4532_, 1);
v_exprs_4539_ = lean_ctor_get(v_toGoalState_4532_, 2);
v_parents_4540_ = lean_ctor_get(v_toGoalState_4532_, 3);
v_congrTable_4541_ = lean_ctor_get(v_toGoalState_4532_, 4);
v_appMap_4542_ = lean_ctor_get(v_toGoalState_4532_, 5);
v_indicesFound_4543_ = lean_ctor_get(v_toGoalState_4532_, 6);
v_newFacts_4544_ = lean_ctor_get(v_toGoalState_4532_, 7);
v_inconsistent_4545_ = lean_ctor_get_uint8(v_toGoalState_4532_, sizeof(void*)*17);
v_nextIdx_4546_ = lean_ctor_get(v_toGoalState_4532_, 8);
v_newRawFacts_4547_ = lean_ctor_get(v_toGoalState_4532_, 9);
v_facts_4548_ = lean_ctor_get(v_toGoalState_4532_, 10);
v_extThms_4549_ = lean_ctor_get(v_toGoalState_4532_, 11);
v_ematch_4550_ = lean_ctor_get(v_toGoalState_4532_, 12);
v_inj_4551_ = lean_ctor_get(v_toGoalState_4532_, 13);
v_split_4552_ = lean_ctor_get(v_toGoalState_4532_, 14);
v_clean_4553_ = lean_ctor_get(v_toGoalState_4532_, 15);
v_sstates_4554_ = lean_ctor_get(v_toGoalState_4532_, 16);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_toGoalState_4532_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4556_ = v_toGoalState_4532_;
v_isShared_4557_ = v_isSharedCheck_4567_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_sstates_4554_);
lean_inc(v_clean_4553_);
lean_inc(v_split_4552_);
lean_inc(v_inj_4551_);
lean_inc(v_ematch_4550_);
lean_inc(v_extThms_4549_);
lean_inc(v_facts_4548_);
lean_inc(v_newRawFacts_4547_);
lean_inc(v_nextIdx_4546_);
lean_inc(v_newFacts_4544_);
lean_inc(v_indicesFound_4543_);
lean_inc(v_appMap_4542_);
lean_inc(v_congrTable_4541_);
lean_inc(v_parents_4540_);
lean_inc(v_exprs_4539_);
lean_inc(v_enodeMap_4538_);
lean_inc(v_nextDeclIdx_4537_);
lean_dec(v_toGoalState_4532_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4567_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___x_4560_; 
v___x_4558_ = lean_array_pop(v_newFacts_4544_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 7, v___x_4558_);
v___x_4560_ = v___x_4556_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_nextDeclIdx_4537_);
lean_ctor_set(v_reuseFailAlloc_4566_, 1, v_enodeMap_4538_);
lean_ctor_set(v_reuseFailAlloc_4566_, 2, v_exprs_4539_);
lean_ctor_set(v_reuseFailAlloc_4566_, 3, v_parents_4540_);
lean_ctor_set(v_reuseFailAlloc_4566_, 4, v_congrTable_4541_);
lean_ctor_set(v_reuseFailAlloc_4566_, 5, v_appMap_4542_);
lean_ctor_set(v_reuseFailAlloc_4566_, 6, v_indicesFound_4543_);
lean_ctor_set(v_reuseFailAlloc_4566_, 7, v___x_4558_);
lean_ctor_set(v_reuseFailAlloc_4566_, 8, v_nextIdx_4546_);
lean_ctor_set(v_reuseFailAlloc_4566_, 9, v_newRawFacts_4547_);
lean_ctor_set(v_reuseFailAlloc_4566_, 10, v_facts_4548_);
lean_ctor_set(v_reuseFailAlloc_4566_, 11, v_extThms_4549_);
lean_ctor_set(v_reuseFailAlloc_4566_, 12, v_ematch_4550_);
lean_ctor_set(v_reuseFailAlloc_4566_, 13, v_inj_4551_);
lean_ctor_set(v_reuseFailAlloc_4566_, 14, v_split_4552_);
lean_ctor_set(v_reuseFailAlloc_4566_, 15, v_clean_4553_);
lean_ctor_set(v_reuseFailAlloc_4566_, 16, v_sstates_4554_);
lean_ctor_set_uint8(v_reuseFailAlloc_4566_, sizeof(void*)*17, v_inconsistent_4545_);
v___x_4560_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
lean_object* v___x_4562_; 
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4560_);
v___x_4562_ = v___x_4535_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4560_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_mvarId_4533_);
v___x_4562_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = lean_st_ref_put(v_a_4518_, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4530_);
return v___x_4564_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4569_);
lean_dec(v_a_4569_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4572_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec(v_a_4584_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4596_, lean_object* v_rhs_4597_, lean_object* v_proof_4598_, uint8_t v_isHEq_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v___x_4611_; 
v___x_4611_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4596_, v_rhs_4597_, v_proof_4598_, v_isHEq_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v___x_4612_; 
lean_dec_ref_known(v___x_4611_, 1);
lean_inc(v_a_4609_);
lean_inc_ref(v_a_4608_);
lean_inc(v_a_4607_);
lean_inc_ref(v_a_4606_);
lean_inc(v_a_4605_);
lean_inc_ref(v_a_4604_);
lean_inc(v_a_4603_);
lean_inc_ref(v_a_4602_);
lean_inc(v_a_4601_);
lean_inc(v_a_4600_);
v___x_4612_ = lean_grind_process_new_facts(v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
return v___x_4612_;
}
else
{
return v___x_4611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4613_, lean_object* v_rhs_4614_, lean_object* v_proof_4615_, lean_object* v_isHEq_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
uint8_t v_isHEq_boxed_4628_; lean_object* v_res_4629_; 
v_isHEq_boxed_4628_ = lean_unbox(v_isHEq_4616_);
v_res_4629_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4613_, v_rhs_4614_, v_proof_4615_, v_isHEq_boxed_4628_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec(v_a_4617_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4630_, lean_object* v_rhs_4631_, lean_object* v_proof_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
uint8_t v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = 0;
v___x_4645_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4630_, v_rhs_4631_, v_proof_4632_, v___x_4644_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4646_, lean_object* v_rhs_4647_, lean_object* v_proof_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4646_, v_rhs_4647_, v_proof_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec(v_a_4649_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4661_, lean_object* v_rhs_4662_, lean_object* v_proof_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
uint8_t v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = 1;
v___x_4676_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4661_, v_rhs_4662_, v_proof_4663_, v___x_4675_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4677_, lean_object* v_rhs_4678_, lean_object* v_proof_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4677_, v_rhs_4678_, v_proof_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___x_4695_; lean_object* v_toGoalState_4696_; lean_object* v_mvarId_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4733_; 
v___x_4695_ = lean_st_ref_take(v_a_4693_);
v_toGoalState_4696_ = lean_ctor_get(v___x_4695_, 0);
v_mvarId_4697_ = lean_ctor_get(v___x_4695_, 1);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4699_ = v___x_4695_;
v_isShared_4700_ = v_isSharedCheck_4733_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_mvarId_4697_);
lean_inc(v_toGoalState_4696_);
lean_dec(v___x_4695_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4733_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_nextDeclIdx_4701_; lean_object* v_enodeMap_4702_; lean_object* v_exprs_4703_; lean_object* v_parents_4704_; lean_object* v_congrTable_4705_; lean_object* v_appMap_4706_; lean_object* v_indicesFound_4707_; lean_object* v_newFacts_4708_; uint8_t v_inconsistent_4709_; lean_object* v_nextIdx_4710_; lean_object* v_newRawFacts_4711_; lean_object* v_facts_4712_; lean_object* v_extThms_4713_; lean_object* v_ematch_4714_; lean_object* v_inj_4715_; lean_object* v_split_4716_; lean_object* v_clean_4717_; lean_object* v_sstates_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4732_; 
v_nextDeclIdx_4701_ = lean_ctor_get(v_toGoalState_4696_, 0);
v_enodeMap_4702_ = lean_ctor_get(v_toGoalState_4696_, 1);
v_exprs_4703_ = lean_ctor_get(v_toGoalState_4696_, 2);
v_parents_4704_ = lean_ctor_get(v_toGoalState_4696_, 3);
v_congrTable_4705_ = lean_ctor_get(v_toGoalState_4696_, 4);
v_appMap_4706_ = lean_ctor_get(v_toGoalState_4696_, 5);
v_indicesFound_4707_ = lean_ctor_get(v_toGoalState_4696_, 6);
v_newFacts_4708_ = lean_ctor_get(v_toGoalState_4696_, 7);
v_inconsistent_4709_ = lean_ctor_get_uint8(v_toGoalState_4696_, sizeof(void*)*17);
v_nextIdx_4710_ = lean_ctor_get(v_toGoalState_4696_, 8);
v_newRawFacts_4711_ = lean_ctor_get(v_toGoalState_4696_, 9);
v_facts_4712_ = lean_ctor_get(v_toGoalState_4696_, 10);
v_extThms_4713_ = lean_ctor_get(v_toGoalState_4696_, 11);
v_ematch_4714_ = lean_ctor_get(v_toGoalState_4696_, 12);
v_inj_4715_ = lean_ctor_get(v_toGoalState_4696_, 13);
v_split_4716_ = lean_ctor_get(v_toGoalState_4696_, 14);
v_clean_4717_ = lean_ctor_get(v_toGoalState_4696_, 15);
v_sstates_4718_ = lean_ctor_get(v_toGoalState_4696_, 16);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_toGoalState_4696_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4720_ = v_toGoalState_4696_;
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_sstates_4718_);
lean_inc(v_clean_4717_);
lean_inc(v_split_4716_);
lean_inc(v_inj_4715_);
lean_inc(v_ematch_4714_);
lean_inc(v_extThms_4713_);
lean_inc(v_facts_4712_);
lean_inc(v_newRawFacts_4711_);
lean_inc(v_nextIdx_4710_);
lean_inc(v_newFacts_4708_);
lean_inc(v_indicesFound_4707_);
lean_inc(v_appMap_4706_);
lean_inc(v_congrTable_4705_);
lean_inc(v_parents_4704_);
lean_inc(v_exprs_4703_);
lean_inc(v_enodeMap_4702_);
lean_inc(v_nextDeclIdx_4701_);
lean_dec(v_toGoalState_4696_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4732_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4722_ = lean_box(0);
v___x_4723_ = l_Lean_PersistentArray_push___redArg(v_facts_4712_, v_fact_4692_);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 10, v___x_4723_);
v___x_4725_ = v___x_4720_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_nextDeclIdx_4701_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_enodeMap_4702_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_exprs_4703_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_parents_4704_);
lean_ctor_set(v_reuseFailAlloc_4731_, 4, v_congrTable_4705_);
lean_ctor_set(v_reuseFailAlloc_4731_, 5, v_appMap_4706_);
lean_ctor_set(v_reuseFailAlloc_4731_, 6, v_indicesFound_4707_);
lean_ctor_set(v_reuseFailAlloc_4731_, 7, v_newFacts_4708_);
lean_ctor_set(v_reuseFailAlloc_4731_, 8, v_nextIdx_4710_);
lean_ctor_set(v_reuseFailAlloc_4731_, 9, v_newRawFacts_4711_);
lean_ctor_set(v_reuseFailAlloc_4731_, 10, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4731_, 11, v_extThms_4713_);
lean_ctor_set(v_reuseFailAlloc_4731_, 12, v_ematch_4714_);
lean_ctor_set(v_reuseFailAlloc_4731_, 13, v_inj_4715_);
lean_ctor_set(v_reuseFailAlloc_4731_, 14, v_split_4716_);
lean_ctor_set(v_reuseFailAlloc_4731_, 15, v_clean_4717_);
lean_ctor_set(v_reuseFailAlloc_4731_, 16, v_sstates_4718_);
lean_ctor_set_uint8(v_reuseFailAlloc_4731_, sizeof(void*)*17, v_inconsistent_4709_);
v___x_4725_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4727_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v___x_4725_);
v___x_4727_ = v___x_4699_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4725_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_mvarId_4697_);
v___x_4727_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_st_ref_put(v_a_4693_, v___x_4727_);
v___x_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4722_);
return v___x_4729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4734_, v_a_4735_);
lean_dec(v_a_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4738_, v_a_4739_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec(v_a_4752_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4764_, lean_object* v_rhs_4765_, lean_object* v_proof_4766_, lean_object* v_generation_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4779_; 
lean_inc_ref(v_rhs_4765_);
lean_inc_ref(v_lhs_4764_);
v___x_4779_ = l_Lean_Meta_mkEq(v_lhs_4764_, v_rhs_4765_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4791_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_n(v_a_4780_, 2);
lean_dec_ref_known(v___x_4779_, 1);
v___x_4781_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4780_, v_a_4768_);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4791_ == 0)
{
lean_object* v_unused_4792_; 
v_unused_4792_ = lean_ctor_get(v___x_4781_, 0);
lean_dec(v_unused_4792_);
v___x_4783_ = v___x_4781_;
v_isShared_4784_ = v_isSharedCheck_4791_;
goto v_resetjp_4782_;
}
else
{
lean_dec(v___x_4781_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4791_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
lean_ctor_set_tag(v___x_4783_, 1);
lean_ctor_set(v___x_4783_, 0, v_a_4780_);
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4780_);
v___x_4786_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; 
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc_ref(v_a_4774_);
lean_inc(v_a_4773_);
lean_inc_ref(v_a_4772_);
lean_inc(v_a_4771_);
lean_inc_ref(v_a_4770_);
lean_inc(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v___x_4786_);
lean_inc(v_generation_4767_);
lean_inc_ref(v_lhs_4764_);
v___x_4787_ = lean_grind_internalize(v_lhs_4764_, v_generation_4767_, v___x_4786_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v___x_4788_; 
lean_dec_ref_known(v___x_4787_, 1);
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc_ref(v_a_4774_);
lean_inc(v_a_4773_);
lean_inc_ref(v_a_4772_);
lean_inc(v_a_4771_);
lean_inc_ref(v_a_4770_);
lean_inc(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v_rhs_4765_);
v___x_4788_ = lean_grind_internalize(v_rhs_4765_, v_generation_4767_, v___x_4786_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v___x_4789_; 
lean_dec_ref_known(v___x_4788_, 1);
v___x_4789_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4764_, v_rhs_4765_, v_proof_4766_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
return v___x_4789_;
}
else
{
lean_dec_ref(v_proof_4766_);
lean_dec_ref(v_rhs_4765_);
lean_dec_ref(v_lhs_4764_);
return v___x_4788_;
}
}
else
{
lean_dec_ref(v___x_4786_);
lean_dec(v_generation_4767_);
lean_dec_ref(v_proof_4766_);
lean_dec_ref(v_rhs_4765_);
lean_dec_ref(v_lhs_4764_);
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_generation_4767_);
lean_dec_ref(v_proof_4766_);
lean_dec_ref(v_rhs_4765_);
lean_dec_ref(v_lhs_4764_);
v_a_4793_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4779_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4779_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4801_, lean_object* v_rhs_4802_, lean_object* v_proof_4803_, lean_object* v_generation_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4801_, v_rhs_4802_, v_proof_4803_, v_generation_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec(v_a_4805_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4817_, lean_object* v_generation_4818_, lean_object* v_p_4819_, uint8_t v_isNeg_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = lean_box(0);
lean_inc(v_a_4830_);
lean_inc_ref(v_a_4829_);
lean_inc(v_a_4828_);
lean_inc_ref(v_a_4827_);
lean_inc(v_a_4826_);
lean_inc_ref(v_a_4825_);
lean_inc(v_a_4824_);
lean_inc_ref(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc(v_a_4821_);
lean_inc_ref(v_p_4819_);
v___x_4833_ = lean_grind_internalize(v_p_4819_, v_generation_4818_, v___x_4832_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_dec_ref_known(v___x_4833_, 1);
if (v_isNeg_4820_ == 0)
{
lean_object* v___x_4834_; 
v___x_4834_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4825_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v_a_4835_; lean_object* v___x_4836_; 
v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
lean_inc(v_a_4835_);
lean_dec_ref_known(v___x_4834_, 1);
v___x_4836_ = l_Lean_Meta_mkEqTrue(v_proof_4817_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4838_; 
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
lean_inc(v_a_4837_);
lean_dec_ref_known(v___x_4836_, 1);
v___x_4838_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4819_, v_a_4835_, v_a_4837_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
return v___x_4838_;
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec(v_a_4835_);
lean_dec_ref(v_p_4819_);
v_a_4839_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4836_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4836_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v_p_4819_);
lean_dec_ref(v_proof_4817_);
v_a_4847_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4834_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4834_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
else
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4825_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref_known(v___x_4855_, 1);
v___x_4857_ = l_Lean_Meta_mkEqFalse(v_proof_4817_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4859_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v___x_4859_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4819_, v_a_4856_, v_a_4858_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
return v___x_4859_;
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
lean_dec(v_a_4856_);
lean_dec_ref(v_p_4819_);
v_a_4860_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4857_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4857_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec_ref(v_p_4819_);
lean_dec_ref(v_proof_4817_);
v_a_4868_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4855_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4855_);
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
}
else
{
lean_dec_ref(v_p_4819_);
lean_dec_ref(v_proof_4817_);
return v___x_4833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4876_, lean_object* v_generation_4877_, lean_object* v_p_4878_, lean_object* v_isNeg_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_){
_start:
{
uint8_t v_isNeg_boxed_4891_; lean_object* v_res_4892_; 
v_isNeg_boxed_4891_ = lean_unbox(v_isNeg_4879_);
v_res_4892_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4876_, v_generation_4877_, v_p_4878_, v_isNeg_boxed_4891_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec(v_a_4880_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4893_, lean_object* v_generation_4894_, lean_object* v_p_4895_, lean_object* v_lhs_4896_, lean_object* v_rhs_4897_, uint8_t v_isNeg_4898_, uint8_t v_isHEq_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_){
_start:
{
if (v_isNeg_4898_ == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_inc_ref(v_p_4895_);
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v_p_4895_);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc_ref(v_a_4906_);
lean_inc(v_a_4905_);
lean_inc_ref(v_a_4904_);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v___x_4911_);
lean_inc(v_generation_4894_);
lean_inc_ref(v_lhs_4896_);
v___x_4912_ = lean_grind_internalize(v_lhs_4896_, v_generation_4894_, v___x_4911_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v___x_4913_; 
lean_dec_ref_known(v___x_4912_, 1);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc_ref(v_a_4906_);
lean_inc(v_a_4905_);
lean_inc_ref(v_a_4904_);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_rhs_4897_);
v___x_4913_ = lean_grind_internalize(v_rhs_4897_, v_generation_4894_, v___x_4911_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec_ref_known(v___x_4913_, 1);
v___x_4914_ = lean_box(0);
v___x_4915_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4895_, v___x_4914_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v___x_4916_; 
lean_dec_ref_known(v___x_4915_, 1);
v___x_4916_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4896_, v_rhs_4897_, v_proof_4893_, v_isHEq_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
return v___x_4916_;
}
else
{
lean_dec_ref(v_rhs_4897_);
lean_dec_ref(v_lhs_4896_);
lean_dec_ref(v_proof_4893_);
return v___x_4915_;
}
}
else
{
lean_dec_ref(v_rhs_4897_);
lean_dec_ref(v_lhs_4896_);
lean_dec_ref(v_p_4895_);
lean_dec_ref(v_proof_4893_);
return v___x_4913_;
}
}
else
{
lean_dec_ref_known(v___x_4911_, 1);
lean_dec_ref(v_rhs_4897_);
lean_dec_ref(v_lhs_4896_);
lean_dec_ref(v_p_4895_);
lean_dec(v_generation_4894_);
lean_dec_ref(v_proof_4893_);
return v___x_4912_;
}
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_dec_ref(v_rhs_4897_);
lean_dec_ref(v_lhs_4896_);
v___x_4917_ = lean_box(0);
lean_inc(v_a_4909_);
lean_inc_ref(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc_ref(v_a_4906_);
lean_inc(v_a_4905_);
lean_inc_ref(v_a_4904_);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_p_4895_);
v___x_4918_ = lean_grind_internalize(v_p_4895_, v_generation_4894_, v___x_4917_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref_known(v___x_4918_, 1);
v___x_4919_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4904_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4921_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = l_Lean_Meta_mkEqFalse(v_proof_4893_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4923_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
v___x_4923_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4895_, v_a_4920_, v_a_4922_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
return v___x_4923_;
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_dec(v_a_4920_);
lean_dec_ref(v_p_4895_);
v_a_4924_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4921_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4921_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec_ref(v_p_4895_);
lean_dec_ref(v_proof_4893_);
v_a_4932_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4919_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4919_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
else
{
lean_dec_ref(v_p_4895_);
lean_dec_ref(v_proof_4893_);
return v___x_4918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4940_ = _args[0];
lean_object* v_generation_4941_ = _args[1];
lean_object* v_p_4942_ = _args[2];
lean_object* v_lhs_4943_ = _args[3];
lean_object* v_rhs_4944_ = _args[4];
lean_object* v_isNeg_4945_ = _args[5];
lean_object* v_isHEq_4946_ = _args[6];
lean_object* v_a_4947_ = _args[7];
lean_object* v_a_4948_ = _args[8];
lean_object* v_a_4949_ = _args[9];
lean_object* v_a_4950_ = _args[10];
lean_object* v_a_4951_ = _args[11];
lean_object* v_a_4952_ = _args[12];
lean_object* v_a_4953_ = _args[13];
lean_object* v_a_4954_ = _args[14];
lean_object* v_a_4955_ = _args[15];
lean_object* v_a_4956_ = _args[16];
lean_object* v_a_4957_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4958_; uint8_t v_isHEq_boxed_4959_; lean_object* v_res_4960_; 
v_isNeg_boxed_4958_ = lean_unbox(v_isNeg_4945_);
v_isHEq_boxed_4959_ = lean_unbox(v_isHEq_4946_);
v_res_4960_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4940_, v_generation_4941_, v_p_4942_, v_lhs_4943_, v_rhs_4944_, v_isNeg_boxed_4958_, v_isHEq_boxed_4959_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec(v_a_4947_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4964_, lean_object* v_generation_4965_, lean_object* v_p_4966_, uint8_t v_isNeg_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v___x_4979_; 
lean_inc_ref(v_p_4966_);
v___x_4979_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4966_, v_a_4975_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4979_, 1);
v___x_4981_ = l_Lean_Expr_cleanupAnnotations(v_a_4980_);
v___x_4982_ = l_Lean_Expr_isApp(v___x_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
lean_dec_ref(v___x_4981_);
v___x_4983_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_4983_;
}
else
{
lean_object* v_arg_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; 
v_arg_4984_ = lean_ctor_get(v___x_4981_, 1);
lean_inc_ref(v_arg_4984_);
v___x_4985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4981_);
v___x_4986_ = l_Lean_Expr_isApp(v___x_4985_);
if (v___x_4986_ == 0)
{
lean_object* v___x_4987_; 
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_arg_4984_);
v___x_4987_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_4987_;
}
else
{
lean_object* v_arg_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
v_arg_4988_ = lean_ctor_get(v___x_4985_, 1);
lean_inc_ref(v_arg_4988_);
v___x_4989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4985_);
v___x_4990_ = l_Lean_Expr_isApp(v___x_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_dec_ref(v___x_4989_);
lean_dec_ref(v_arg_4988_);
lean_dec_ref(v_arg_4984_);
v___x_4991_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_4991_;
}
else
{
lean_object* v_arg_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; uint8_t v___x_4995_; 
v_arg_4992_ = lean_ctor_get(v___x_4989_, 1);
lean_inc_ref(v_arg_4992_);
v___x_4993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4989_);
v___x_4994_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4995_ = l_Lean_Expr_isConstOf(v___x_4993_, v___x_4994_);
if (v___x_4995_ == 0)
{
uint8_t v___x_4996_; 
lean_dec_ref(v_arg_4988_);
v___x_4996_ = l_Lean_Expr_isApp(v___x_4993_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
lean_dec_ref(v___x_4993_);
lean_dec_ref(v_arg_4992_);
lean_dec_ref(v_arg_4984_);
v___x_4997_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_4997_;
}
else
{
lean_object* v___x_4998_; lean_object* v___x_4999_; uint8_t v___x_5000_; 
v___x_4998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4993_);
v___x_4999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5000_ = l_Lean_Expr_isConstOf(v___x_4998_, v___x_4999_);
lean_dec_ref(v___x_4998_);
if (v___x_5000_ == 0)
{
lean_object* v___x_5001_; 
lean_dec_ref(v_arg_4992_);
lean_dec_ref(v_arg_4984_);
v___x_5001_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_5001_;
}
else
{
lean_object* v___x_5002_; 
v___x_5002_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4964_, v_generation_4965_, v_p_4966_, v_arg_4992_, v_arg_4984_, v_isNeg_4967_, v___x_5000_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_5002_;
}
}
}
else
{
uint8_t v___x_5003_; 
lean_dec_ref(v___x_4993_);
v___x_5003_ = l_Lean_Expr_isProp(v_arg_4992_);
lean_dec_ref(v_arg_4992_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4964_, v_generation_4965_, v_p_4966_, v_arg_4988_, v_arg_4984_, v_isNeg_4967_, v___x_5003_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_5004_;
}
else
{
lean_object* v___x_5005_; 
lean_dec_ref(v_arg_4988_);
lean_dec_ref(v_arg_4984_);
v___x_5005_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4964_, v_generation_4965_, v_p_4966_, v_isNeg_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
return v___x_5005_;
}
}
}
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec_ref(v_p_4966_);
lean_dec(v_generation_4965_);
lean_dec_ref(v_proof_4964_);
v_a_5006_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4979_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4979_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5014_, lean_object* v_generation_5015_, lean_object* v_p_5016_, lean_object* v_isNeg_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_){
_start:
{
uint8_t v_isNeg_boxed_5029_; lean_object* v_res_5030_; 
v_isNeg_boxed_5029_ = lean_unbox(v_isNeg_5017_);
v_res_5030_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5014_, v_generation_5015_, v_p_5016_, v_isNeg_boxed_5029_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
lean_dec(v_a_5027_);
lean_dec_ref(v_a_5026_);
lean_dec(v_a_5025_);
lean_dec_ref(v_a_5024_);
lean_dec(v_a_5023_);
lean_dec_ref(v_a_5022_);
lean_dec(v_a_5021_);
lean_dec_ref(v_a_5020_);
lean_dec(v_a_5019_);
lean_dec(v_a_5018_);
return v_res_5030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5039_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5040_ = l_Lean_Name_append(v___x_5039_, v___x_5038_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5041_, lean_object* v_proof_5042_, lean_object* v_generation_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5076_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___x_5086_; lean_object* v_toCold_5087_; lean_object* v_options_5088_; uint8_t v_hasTrace_5089_; 
lean_inc_ref(v_fact_5041_);
v___x_5086_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5041_, v_a_5044_);
lean_dec_ref(v___x_5086_);
v_toCold_5087_ = lean_ctor_get(v_a_5052_, 0);
v_options_5088_ = lean_ctor_get(v_toCold_5087_, 2);
v_hasTrace_5089_ = lean_ctor_get_uint8(v_options_5088_, sizeof(void*)*1);
if (v_hasTrace_5089_ == 0)
{
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
v___y_5074_ = v_a_5049_;
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
goto v___jp_5068_;
}
else
{
lean_object* v_inheritedTraceOptions_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; 
v_inheritedTraceOptions_5090_ = lean_ctor_get(v_toCold_5087_, 11);
v___x_5091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5090_, v_options_5088_, v___x_5092_);
if (v___x_5093_ == 0)
{
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
v___y_5074_ = v_a_5049_;
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
goto v___jp_5068_;
}
else
{
lean_object* v___x_5094_; 
v___x_5094_ = l_Lean_Meta_Grind_updateLastTag(v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_dec_ref_known(v___x_5094_, 1);
lean_inc_ref(v_fact_5041_);
v___x_5095_ = l_Lean_MessageData_ofExpr(v_fact_5041_);
v___x_5096_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5091_, v___x_5095_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_dec_ref_known(v___x_5096_, 1);
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
v___y_5074_ = v_a_5049_;
v___y_5075_ = v_a_5050_;
v___y_5076_ = v_a_5051_;
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
goto v___jp_5068_;
}
else
{
lean_dec(v_generation_5043_);
lean_dec_ref(v_proof_5042_);
lean_dec_ref(v_fact_5041_);
return v___x_5096_;
}
}
else
{
lean_dec(v_generation_5043_);
lean_dec_ref(v_proof_5042_);
lean_dec_ref(v_fact_5041_);
return v___x_5094_;
}
}
}
v___jp_5055_:
{
uint8_t v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = 0;
v___x_5067_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5042_, v_generation_5043_, v_fact_5041_, v___x_5066_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
return v___x_5067_;
}
v___jp_5068_:
{
lean_object* v___x_5079_; uint8_t v___x_5080_; 
lean_inc_ref(v_fact_5041_);
v___x_5079_ = l_Lean_Expr_cleanupAnnotations(v_fact_5041_);
v___x_5080_ = l_Lean_Expr_isApp(v___x_5079_);
if (v___x_5080_ == 0)
{
lean_dec_ref(v___x_5079_);
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
v___y_5060_ = v___y_5073_;
v___y_5061_ = v___y_5074_;
v___y_5062_ = v___y_5075_;
v___y_5063_ = v___y_5076_;
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
goto v___jp_5055_;
}
else
{
lean_object* v_arg_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; uint8_t v___x_5084_; 
v_arg_5081_ = lean_ctor_get(v___x_5079_, 1);
lean_inc_ref(v_arg_5081_);
v___x_5082_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5079_);
v___x_5083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5084_ = l_Lean_Expr_isConstOf(v___x_5082_, v___x_5083_);
lean_dec_ref(v___x_5082_);
if (v___x_5084_ == 0)
{
lean_dec_ref(v_arg_5081_);
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
v___y_5060_ = v___y_5073_;
v___y_5061_ = v___y_5074_;
v___y_5062_ = v___y_5075_;
v___y_5063_ = v___y_5076_;
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
goto v___jp_5055_;
}
else
{
lean_object* v___x_5085_; 
lean_dec_ref(v_fact_5041_);
v___x_5085_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5042_, v_generation_5043_, v_arg_5081_, v___x_5084_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
return v___x_5085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5097_, lean_object* v_proof_5098_, lean_object* v_generation_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5097_, v_proof_5098_, v_generation_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec_ref(v_a_5104_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec(v_a_5100_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_){
_start:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5115_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; uint8_t v___x_5128_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5126_, 1);
v___x_5128_ = lean_unbox(v_a_5127_);
lean_dec(v_a_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5130_ = l_Lean_Core_checkSystem(v___x_5129_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v___x_5131_; 
lean_dec_ref_known(v___x_5130_, 1);
v___x_5131_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5115_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5168_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5134_ = v___x_5131_;
v_isShared_5135_ = v_isSharedCheck_5168_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5131_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5168_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
if (lean_obj_tag(v_a_5132_) == 1)
{
lean_object* v_val_5136_; 
lean_del_object(v___x_5134_);
v_val_5136_ = lean_ctor_get(v_a_5132_, 0);
lean_inc(v_val_5136_);
lean_dec_ref_known(v_a_5132_, 1);
if (lean_obj_tag(v_val_5136_) == 0)
{
lean_object* v_lhs_5137_; lean_object* v_rhs_5138_; lean_object* v_proof_5139_; uint8_t v_isHEq_5140_; lean_object* v___x_5141_; 
v_lhs_5137_ = lean_ctor_get(v_val_5136_, 0);
lean_inc_ref(v_lhs_5137_);
v_rhs_5138_ = lean_ctor_get(v_val_5136_, 1);
lean_inc_ref(v_rhs_5138_);
v_proof_5139_ = lean_ctor_get(v_val_5136_, 2);
lean_inc_ref(v_proof_5139_);
v_isHEq_5140_ = lean_ctor_get_uint8(v_val_5136_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5136_, 3);
v___x_5141_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5137_, v_rhs_5138_, v_proof_5139_, v_isHEq_5140_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_dec_ref_known(v___x_5141_, 1);
goto _start;
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
v_a_5143_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5141_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5141_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_object* v_prop_5151_; lean_object* v_proof_5152_; lean_object* v_generation_5153_; lean_object* v___x_5154_; 
v_prop_5151_ = lean_ctor_get(v_val_5136_, 0);
lean_inc_ref(v_prop_5151_);
v_proof_5152_ = lean_ctor_get(v_val_5136_, 1);
lean_inc_ref(v_proof_5152_);
v_generation_5153_ = lean_ctor_get(v_val_5136_, 2);
lean_inc(v_generation_5153_);
lean_dec_ref_known(v_val_5136_, 3);
v___x_5154_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5151_, v_proof_5152_, v_generation_5153_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_dec_ref_known(v___x_5154_, 1);
goto _start;
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
v_a_5156_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5154_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5154_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
lean_dec(v_a_5132_);
v___x_5164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5164_);
v___x_5166_ = v___x_5134_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
v_a_5169_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5131_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5131_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
v_a_5177_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5130_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5130_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
else
{
lean_object* v___x_5185_; 
v___x_5185_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5115_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5193_; 
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5193_ == 0)
{
lean_object* v_unused_5194_; 
v_unused_5194_ = lean_ctor_get(v___x_5185_, 0);
lean_dec(v_unused_5194_);
v___x_5187_ = v___x_5185_;
v_isShared_5188_ = v_isSharedCheck_5193_;
goto v_resetjp_5186_;
}
else
{
lean_dec(v___x_5185_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5193_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5189_; lean_object* v___x_5191_; 
v___x_5189_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5188_ == 0)
{
lean_ctor_set(v___x_5187_, 0, v___x_5189_);
v___x_5191_ = v___x_5187_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___x_5189_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
v_a_5195_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5185_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5185_);
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
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
v_a_5203_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5126_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5126_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
lean_object* v_res_5222_; 
v_res_5222_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec(v___y_5211_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; 
v___x_5234_ = lean_box(0);
v___x_5235_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec(v_a_5223_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5248_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5238_ = v___x_5235_;
v_isShared_5239_ = v_isSharedCheck_5248_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5235_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5248_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v_fst_5240_; 
v_fst_5240_ = lean_ctor_get(v_a_5236_, 0);
lean_inc(v_fst_5240_);
lean_dec(v_a_5236_);
if (lean_obj_tag(v_fst_5240_) == 0)
{
lean_object* v___x_5242_; 
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 0, v___x_5234_);
v___x_5242_ = v___x_5238_;
goto v_reusejp_5241_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5234_);
v___x_5242_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5241_;
}
v_reusejp_5241_:
{
return v___x_5242_;
}
}
else
{
lean_object* v_val_5244_; lean_object* v___x_5246_; 
v_val_5244_ = lean_ctor_get(v_fst_5240_, 0);
lean_inc(v_val_5244_);
lean_dec_ref_known(v_fst_5240_, 1);
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 0, v_val_5244_);
v___x_5246_ = v___x_5238_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_val_5244_);
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
v_a_5249_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5235_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5235_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = lean_grind_process_new_facts(v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5269_, lean_object* v_a_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5283_, lean_object* v_a_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5283_, v_a_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v_a_5284_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5297_, lean_object* v_proof_5298_, lean_object* v_generation_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
uint8_t v___x_5311_; 
lean_inc_ref(v_fact_5297_);
v___x_5311_ = l_Lean_Expr_isTrue(v_fact_5297_);
if (v___x_5311_ == 0)
{
lean_object* v___x_5312_; 
v___x_5312_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5300_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5324_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5324_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5324_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
uint8_t v___x_5317_; 
v___x_5317_ = lean_unbox(v_a_5313_);
lean_dec(v_a_5313_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; lean_object* v___x_5319_; 
lean_del_object(v___x_5315_);
v___x_5318_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5300_);
lean_dec_ref(v___x_5318_);
v___x_5319_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5297_, v_proof_5298_, v_generation_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
return v___x_5319_;
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
lean_dec(v_generation_5299_);
lean_dec_ref(v_proof_5298_);
lean_dec_ref(v_fact_5297_);
v___x_5320_ = lean_box(0);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5320_);
v___x_5322_ = v___x_5315_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec(v_generation_5299_);
lean_dec_ref(v_proof_5298_);
lean_dec_ref(v_fact_5297_);
v_a_5325_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5312_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5312_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
else
{
lean_object* v___x_5333_; lean_object* v___x_5334_; 
lean_dec(v_generation_5299_);
lean_dec_ref(v_proof_5298_);
lean_dec_ref(v_fact_5297_);
v___x_5333_ = lean_box(0);
v___x_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5333_);
return v___x_5334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5335_, lean_object* v_proof_5336_, lean_object* v_generation_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Meta_Grind_add(v_fact_5335_, v_proof_5336_, v_generation_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
lean_dec(v_a_5345_);
lean_dec_ref(v_a_5344_);
lean_dec(v_a_5343_);
lean_dec_ref(v_a_5342_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec(v_a_5338_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5350_, lean_object* v_generation_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
lean_object* v___x_5363_; 
lean_inc(v_fvarId_5350_);
v___x_5363_ = l_Lean_FVarId_getType___redArg(v_fvarId_5350_, v_a_5358_, v_a_5360_, v_a_5361_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
lean_dec_ref_known(v___x_5363_, 1);
v___x_5365_ = l_Lean_mkFVar(v_fvarId_5350_);
v___x_5366_ = l_Lean_Meta_Grind_add(v_a_5364_, v___x_5365_, v_generation_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
return v___x_5366_;
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec(v_generation_5351_);
lean_dec(v_fvarId_5350_);
v_a_5367_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5363_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5363_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5375_, lean_object* v_generation_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5375_, v_generation_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
lean_dec(v_a_5384_);
lean_dec_ref(v_a_5383_);
lean_dec(v_a_5382_);
lean_dec_ref(v_a_5381_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec(v_a_5377_);
return v_res_5388_;
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
