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
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(lean_object* v_e_1_, uint8_t v_flippedNew_2_, lean_object* v_targetNew_x3f_3_, lean_object* v_proofNew_x3f_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
uint8_t v_flippedNew_2_ = stack[1].m_num;
lean_object* v_targetNew_x3f_3_ = stack[2].m_obj;
lean_object* v_proofNew_x3f_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_1_, v_flippedNew_2_, v_targetNew_x3f_3_, v_proofNew_x3f_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* v_e_64_, lean_object* v_flippedNew_65_, lean_object* v_targetNew_x3f_66_, lean_object* v_proofNew_x3f_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
uint8_t v_flippedNew_boxed_74_; lean_object* v_res_75_; 
v_flippedNew_boxed_74_ = lean_unbox(v_flippedNew_65_);
v_res_75_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_64_, v_flippedNew_boxed_74_, v_targetNew_x3f_66_, v_proofNew_x3f_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
return v_res_75_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* v_e_76_, uint8_t v_flippedNew_77_, lean_object* v_targetNew_x3f_78_, lean_object* v_proofNew_x3f_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_76_, v_flippedNew_77_, v_targetNew_x3f_78_, v_proofNew_x3f_79_, v_a_80_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_91_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_76_ = stack[0].m_obj;
uint8_t v_flippedNew_77_ = stack[1].m_num;
lean_object* v_targetNew_x3f_78_ = stack[2].m_obj;
lean_object* v_proofNew_x3f_79_ = stack[3].m_obj;
lean_object* v_a_80_ = stack[4].m_obj;
lean_object* v_a_81_ = stack[5].m_obj;
lean_object* v_a_82_ = stack[6].m_obj;
lean_object* v_a_83_ = stack[7].m_obj;
lean_object* v_a_84_ = stack[8].m_obj;
lean_object* v_a_85_ = stack[9].m_obj;
lean_object* v_a_86_ = stack[10].m_obj;
lean_object* v_a_87_ = stack[11].m_obj;
lean_object* v_a_88_ = stack[12].m_obj;
lean_object* v_a_89_ = stack[13].m_obj;
lean_object* v_res_92_;
v_res_92_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(v_e_76_, v_flippedNew_77_, v_targetNew_x3f_78_, v_proofNew_x3f_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* v_e_93_, lean_object* v_flippedNew_94_, lean_object* v_targetNew_x3f_95_, lean_object* v_proofNew_x3f_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
uint8_t v_flippedNew_boxed_108_; lean_object* v_res_109_; 
v_flippedNew_boxed_108_ = lean_unbox(v_flippedNew_94_);
v_res_109_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(v_e_93_, v_flippedNew_boxed_108_, v_targetNew_x3f_95_, v_proofNew_x3f_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec(v_a_97_);
return v_res_109_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* v_e_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = 0;
v___x_118_ = lean_box(0);
v___x_119_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_110_, v___x_117_, v___x_118_, v___x_118_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
return v___x_119_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_110_ = stack[0].m_obj;
lean_object* v_a_111_ = stack[1].m_obj;
lean_object* v_a_112_ = stack[2].m_obj;
lean_object* v_a_113_ = stack[3].m_obj;
lean_object* v_a_114_ = stack[4].m_obj;
lean_object* v_a_115_ = stack[5].m_obj;
lean_object* v_res_120_;
v_res_120_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* v_e_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
return v_res_128_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_129_, v_a_130_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
return v___x_141_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_129_ = stack[0].m_obj;
lean_object* v_a_130_ = stack[1].m_obj;
lean_object* v_a_131_ = stack[2].m_obj;
lean_object* v_a_132_ = stack[3].m_obj;
lean_object* v_a_133_ = stack[4].m_obj;
lean_object* v_a_134_ = stack[5].m_obj;
lean_object* v_a_135_ = stack[6].m_obj;
lean_object* v_a_136_ = stack[7].m_obj;
lean_object* v_a_137_ = stack[8].m_obj;
lean_object* v_a_138_ = stack[9].m_obj;
lean_object* v_a_139_ = stack[10].m_obj;
lean_object* v_res_142_;
v_res_142_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(v_e_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* v_e_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(v_e_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec(v_a_144_);
return v_res_155_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* v_parent_156_){
_start:
{
uint8_t v___y_158_; uint8_t v___x_160_; 
v___x_160_ = l_Lean_Expr_isApp(v_parent_156_);
if (v___x_160_ == 0)
{
v___y_158_ = v___x_160_;
goto v___jp_157_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_isMatchCond(v_parent_156_);
if (v___x_161_ == 0)
{
v___y_158_ = v___x_160_;
goto v___jp_157_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = l_Lean_Expr_isArrow(v_parent_156_);
return v___x_162_;
}
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_Expr_isArrow(v_parent_156_);
return v___x_159_;
}
else
{
return v___y_158_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_156_ = stack[0].m_obj;
uint8_t v_res_163_;
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_156_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_164_);
lean_dec_ref(v_parent_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object* v_msgData_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_env_174_; uint8_t v___x_175_; lean_object* v_env_176_; lean_object* v___x_177_; lean_object* v_toCold_178_; lean_object* v_mctx_179_; lean_object* v_lctx_180_; lean_object* v_options_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_173_ = lean_st_ref_get(v___y_171_);
v_env_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref(v_env_174_);
lean_dec(v___x_173_);
v___x_175_ = 0;
v_env_176_ = l_Lean_Environment_setRecordingDeps(v_env_174_, v___x_175_);
v___x_177_ = lean_st_ref_get(v___y_169_);
v_toCold_178_ = lean_ctor_get(v___y_170_, 0);
v_mctx_179_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_mctx_179_);
lean_dec(v___x_177_);
v_lctx_180_ = lean_ctor_get(v___y_168_, 2);
v_options_181_ = lean_ctor_get(v_toCold_178_, 2);
lean_inc_ref(v_options_181_);
lean_inc_ref(v_lctx_180_);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v_env_176_);
lean_ctor_set(v___x_182_, 1, v_mctx_179_);
lean_ctor_set(v___x_182_, 2, v_lctx_180_);
lean_ctor_set(v___x_182_, 3, v_options_181_);
v___x_183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_msgData_167_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_167_ = stack[0].m_obj;
lean_object* v___y_168_ = stack[1].m_obj;
lean_object* v___y_169_ = stack[2].m_obj;
lean_object* v___y_170_ = stack[3].m_obj;
lean_object* v___y_171_ = stack[4].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_193_; double v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_float_of_nat(v___x_193_);
return v___x_194_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_ref_205_; lean_object* v___x_206_; lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_252_; 
v_ref_205_ = lean_ctor_get(v___y_202_, 2);
v___x_206_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_252_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_252_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_252_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v_traceState_212_; lean_object* v_env_213_; lean_object* v_nextMacroScope_214_; lean_object* v_ngen_215_; lean_object* v_auxDeclNGen_216_; lean_object* v_cache_217_; lean_object* v_recordedDeps_218_; lean_object* v_messages_219_; lean_object* v_infoState_220_; lean_object* v_snapshotTasks_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_251_; 
v___x_211_ = lean_st_ref_take(v___y_203_);
v_traceState_212_ = lean_ctor_get(v___x_211_, 4);
v_env_213_ = lean_ctor_get(v___x_211_, 0);
v_nextMacroScope_214_ = lean_ctor_get(v___x_211_, 1);
v_ngen_215_ = lean_ctor_get(v___x_211_, 2);
v_auxDeclNGen_216_ = lean_ctor_get(v___x_211_, 3);
v_cache_217_ = lean_ctor_get(v___x_211_, 5);
v_recordedDeps_218_ = lean_ctor_get(v___x_211_, 6);
v_messages_219_ = lean_ctor_get(v___x_211_, 7);
v_infoState_220_ = lean_ctor_get(v___x_211_, 8);
v_snapshotTasks_221_ = lean_ctor_get(v___x_211_, 9);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_251_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snapshotTasks_221_);
lean_inc(v_infoState_220_);
lean_inc(v_messages_219_);
lean_inc(v_recordedDeps_218_);
lean_inc(v_cache_217_);
lean_inc(v_traceState_212_);
lean_inc(v_auxDeclNGen_216_);
lean_inc(v_ngen_215_);
lean_inc(v_nextMacroScope_214_);
lean_inc(v_env_213_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_251_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint64_t v_tid_225_; lean_object* v_traces_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_250_; 
v_tid_225_ = lean_ctor_get_uint64(v_traceState_212_, sizeof(void*)*1);
v_traces_226_ = lean_ctor_get(v_traceState_212_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_traceState_212_);
if (v_isSharedCheck_250_ == 0)
{
v___x_228_ = v_traceState_212_;
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_traces_226_);
lean_dec(v_traceState_212_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_250_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; double v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_box(0);
v___x_232_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_233_ = 0;
v___x_234_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_235_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_235_, 0, v_cls_198_);
lean_ctor_set(v___x_235_, 1, v___x_231_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
lean_ctor_set_float(v___x_235_, sizeof(void*)*3, v___x_232_);
lean_ctor_set_float(v___x_235_, sizeof(void*)*3 + 8, v___x_232_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*3 + 16, v___x_233_);
v___x_236_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_237_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v_a_207_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
lean_inc(v_ref_205_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_ref_205_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = l_Lean_PersistentArray_push___redArg(v_traces_226_, v___x_238_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_239_);
v___x_241_ = v___x_228_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_239_);
lean_ctor_set_uint64(v_reuseFailAlloc_249_, sizeof(void*)*1, v_tid_225_);
v___x_241_ = v_reuseFailAlloc_249_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 4, v___x_241_);
v___x_243_ = v___x_223_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_env_213_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_nextMacroScope_214_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_ngen_215_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_auxDeclNGen_216_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_recordedDeps_218_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_messages_219_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_infoState_220_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_snapshotTasks_221_);
v___x_243_ = v_reuseFailAlloc_248_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_st_ref_put(v___y_203_, v___x_243_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_230_);
v___x_246_ = v___x_209_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_230_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_198_ = stack[0].m_obj;
lean_object* v_msg_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v___y_202_ = stack[4].m_obj;
lean_object* v___y_203_ = stack[5].m_obj;
lean_object* v_res_253_;
v_res_253_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_198_, v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_254_, lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_254_, v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_262_, lean_object* v_xs_263_, lean_object* v_v_264_, lean_object* v_i_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_xs_263_);
v___x_267_ = lean_nat_dec_lt(v_i_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v_i_265_);
lean_dec_ref(v_v_264_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_fget_borrowed(v_xs_263_, v_i_265_);
lean_inc_ref(v_v_264_);
lean_inc(v___x_269_);
v___x_270_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_262_, v___x_269_, v_v_264_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_i_265_, v___x_271_);
lean_dec(v_i_265_);
v_i_265_ = v___x_272_;
goto _start;
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_v_264_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_i_265_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_275_, lean_object* v_xs_276_, lean_object* v_v_277_, lean_object* v_i_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_275_, v_xs_276_, v_v_277_, v_i_278_);
lean_dec_ref(v_xs_276_);
lean_dec_ref(v___x_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_280_, lean_object* v_xs_281_, lean_object* v_v_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_280_, v_xs_281_, v_v_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_285_, lean_object* v_xs_286_, lean_object* v_v_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_285_, v_xs_286_, v_v_287_);
lean_dec_ref(v_xs_286_);
lean_dec_ref(v___x_285_);
return v_res_288_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_289_, lean_object* v_x_290_, size_t v_x_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_293_; lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; lean_object* v_j_297_; lean_object* v_entry_298_; 
v_es_293_ = lean_ctor_get(v_x_290_, 0);
v___x_294_ = lean_box(2);
v___x_295_ = ((size_t)31ULL);
v___x_296_ = lean_usize_land(v_x_291_, v___x_295_);
v_j_297_ = lean_usize_to_nat(v___x_296_);
v_entry_298_ = lean_array_get(v___x_294_, v_es_293_, v_j_297_);
switch(lean_obj_tag(v_entry_298_))
{
case 0:
{
lean_object* v_key_299_; uint8_t v___x_300_; 
v_key_299_ = lean_ctor_get(v_entry_298_, 0);
lean_inc(v_key_299_);
lean_dec_ref_known(v_entry_298_, 2);
v___x_300_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_289_, v_x_292_, v_key_299_);
if (v___x_300_ == 0)
{
lean_dec(v_j_297_);
return v_x_290_;
}
else
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_308_; 
lean_inc_ref(v_es_293_);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v_x_290_, 0);
lean_dec(v_unused_309_);
v___x_302_ = v_x_290_;
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_x_290_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_308_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_304_ = lean_array_set(v_es_293_, v_j_297_, v___x_294_);
lean_dec(v_j_297_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_304_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
case 1:
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_344_; 
lean_inc_ref(v_es_293_);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_x_290_, 0);
lean_dec(v_unused_345_);
v___x_311_ = v_x_290_;
v_isShared_312_ = v_isSharedCheck_344_;
goto v_resetjp_310_;
}
else
{
lean_dec(v_x_290_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_344_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_node_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_343_; 
v_node_313_ = lean_ctor_get(v_entry_298_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_entry_298_);
if (v_isSharedCheck_343_ == 0)
{
v___x_315_ = v_entry_298_;
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_node_313_);
lean_dec(v_entry_298_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_343_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
size_t v___x_317_; lean_object* v_entries_318_; size_t v___x_319_; lean_object* v_newNode_320_; lean_object* v___x_321_; 
v___x_317_ = ((size_t)5ULL);
v_entries_318_ = lean_array_set(v_es_293_, v_j_297_, v___x_294_);
v___x_319_ = lean_usize_shift_right(v_x_291_, v___x_317_);
v_newNode_320_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_289_, v_node_313_, v___x_319_, v_x_292_);
lean_inc_ref(v_newNode_320_);
v___x_321_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_323_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_newNode_320_);
v___x_323_ = v___x_315_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_newNode_320_);
v___x_323_ = v_reuseFailAlloc_328_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_array_set(v_entries_318_, v_j_297_, v___x_323_);
lean_dec(v_j_297_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_324_);
v___x_326_ = v___x_311_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v_val_329_; lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_342_; 
lean_dec_ref(v_newNode_320_);
lean_del_object(v___x_315_);
v_val_329_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_321_, 1);
v_fst_330_ = lean_ctor_get(v_val_329_, 0);
v_snd_331_ = lean_ctor_get(v_val_329_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_val_329_);
if (v_isSharedCheck_342_ == 0)
{
v___x_333_ = v_val_329_;
v_isShared_334_ = v_isSharedCheck_342_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_330_);
lean_dec(v_val_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_342_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_snd_331_);
v___x_336_ = v_reuseFailAlloc_341_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_array_set(v_entries_318_, v_j_297_, v___x_336_);
lean_dec(v_j_297_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_337_);
v___x_339_ = v___x_311_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_297_);
lean_dec_ref(v_x_292_);
return v_x_290_;
}
}
}
else
{
lean_object* v_ks_346_; lean_object* v_vs_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_361_; 
v_ks_346_ = lean_ctor_get(v_x_290_, 0);
v_vs_347_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_361_ == 0)
{
v___x_349_ = v_x_290_;
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_vs_347_);
lean_inc(v_ks_346_);
lean_dec(v_x_290_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_289_, v_ks_346_, v_x_292_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v___x_353_; 
if (v_isShared_350_ == 0)
{
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_ks_346_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_vs_347_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
else
{
lean_object* v_val_355_; lean_object* v_keys_x27_356_; lean_object* v_vals_x27_357_; lean_object* v___x_359_; 
v_val_355_ = lean_ctor_get(v___x_351_, 0);
lean_inc_n(v_val_355_, 2);
lean_dec_ref_known(v___x_351_, 1);
v_keys_x27_356_ = l_Array_eraseIdx___redArg(v_ks_346_, v_val_355_);
v_vals_x27_357_ = l_Array_eraseIdx___redArg(v_vs_347_, v_val_355_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_vals_x27_357_);
lean_ctor_set(v___x_349_, 0, v_keys_x27_356_);
v___x_359_ = v___x_349_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_keys_x27_356_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_vals_x27_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_289_ = stack[0].m_obj;
lean_object* v_x_290_ = stack[1].m_obj;
size_t v_x_291_ = stack[2].m_num;
lean_object* v_x_292_ = stack[3].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_289_, v_x_290_, v_x_291_, v_x_292_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
size_t v_x_22722__boxed_367_; lean_object* v_res_368_; 
v_x_22722__boxed_367_ = lean_unbox_usize(v_x_365_);
lean_dec(v_x_365_);
v_res_368_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_363_, v_x_364_, v_x_22722__boxed_367_, v_x_366_);
lean_dec_ref(v___x_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint64_t v___x_372_; size_t v_h_373_; lean_object* v___x_374_; 
lean_inc_ref(v_x_371_);
v___x_372_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_369_, v_x_371_);
v_h_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_369_, v_x_370_, v_h_373_, v_x_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_375_, v_x_376_, v_x_377_);
lean_dec_ref(v___x_375_);
return v_res_378_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_390_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_391_ = l_Lean_Name_append(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_395_, lean_object* v_b_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
if (lean_obj_tag(v_as_x27_395_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_b_396_);
return v___x_408_;
}
else
{
lean_object* v_head_409_; lean_object* v_tail_410_; lean_object* v___x_411_; lean_object* v___y_413_; uint8_t v_a_453_; uint8_t v___x_467_; 
v_head_409_ = lean_ctor_get(v_as_x27_395_, 0);
v_tail_410_ = lean_ctor_get(v_as_x27_395_, 1);
v___x_411_ = lean_box(0);
v___x_467_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_409_);
if (v___x_467_ == 0)
{
v_a_453_ = v___x_467_;
goto v___jp_452_;
}
else
{
lean_object* v___x_468_; 
lean_inc(v_head_409_);
v___x_468_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_409_, v___y_397_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
v_a_453_ = v___x_470_;
goto v___jp_452_;
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_a_471_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_468_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_468_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v_toGoalState_415_; lean_object* v_mvarId_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_451_; 
v___x_414_ = lean_st_ref_take(v___y_413_);
v_toGoalState_415_ = lean_ctor_get(v___x_414_, 0);
v_mvarId_416_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_451_ == 0)
{
v___x_418_ = v___x_414_;
v_isShared_419_ = v_isSharedCheck_451_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_mvarId_416_);
lean_inc(v_toGoalState_415_);
lean_dec(v___x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_451_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v_nextDeclIdx_420_; lean_object* v_enodeMap_421_; lean_object* v_exprs_422_; lean_object* v_parents_423_; lean_object* v_congrTable_424_; lean_object* v_appMap_425_; lean_object* v_indicesFound_426_; lean_object* v_toProcess_427_; uint8_t v_inconsistent_428_; lean_object* v_nextIdx_429_; lean_object* v_newRawFacts_430_; lean_object* v_facts_431_; lean_object* v_extThms_432_; lean_object* v_ematch_433_; lean_object* v_inj_434_; lean_object* v_split_435_; lean_object* v_clean_436_; lean_object* v_sstates_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_450_; 
v_nextDeclIdx_420_ = lean_ctor_get(v_toGoalState_415_, 0);
v_enodeMap_421_ = lean_ctor_get(v_toGoalState_415_, 1);
v_exprs_422_ = lean_ctor_get(v_toGoalState_415_, 2);
v_parents_423_ = lean_ctor_get(v_toGoalState_415_, 3);
v_congrTable_424_ = lean_ctor_get(v_toGoalState_415_, 4);
v_appMap_425_ = lean_ctor_get(v_toGoalState_415_, 5);
v_indicesFound_426_ = lean_ctor_get(v_toGoalState_415_, 6);
v_toProcess_427_ = lean_ctor_get(v_toGoalState_415_, 7);
v_inconsistent_428_ = lean_ctor_get_uint8(v_toGoalState_415_, sizeof(void*)*17);
v_nextIdx_429_ = lean_ctor_get(v_toGoalState_415_, 8);
v_newRawFacts_430_ = lean_ctor_get(v_toGoalState_415_, 9);
v_facts_431_ = lean_ctor_get(v_toGoalState_415_, 10);
v_extThms_432_ = lean_ctor_get(v_toGoalState_415_, 11);
v_ematch_433_ = lean_ctor_get(v_toGoalState_415_, 12);
v_inj_434_ = lean_ctor_get(v_toGoalState_415_, 13);
v_split_435_ = lean_ctor_get(v_toGoalState_415_, 14);
v_clean_436_ = lean_ctor_get(v_toGoalState_415_, 15);
v_sstates_437_ = lean_ctor_get(v_toGoalState_415_, 16);
v_isSharedCheck_450_ = !lean_is_exclusive(v_toGoalState_415_);
if (v_isSharedCheck_450_ == 0)
{
v___x_439_ = v_toGoalState_415_;
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_sstates_437_);
lean_inc(v_clean_436_);
lean_inc(v_split_435_);
lean_inc(v_inj_434_);
lean_inc(v_ematch_433_);
lean_inc(v_extThms_432_);
lean_inc(v_facts_431_);
lean_inc(v_newRawFacts_430_);
lean_inc(v_nextIdx_429_);
lean_inc(v_toProcess_427_);
lean_inc(v_indicesFound_426_);
lean_inc(v_appMap_425_);
lean_inc(v_congrTable_424_);
lean_inc(v_parents_423_);
lean_inc(v_exprs_422_);
lean_inc(v_enodeMap_421_);
lean_inc(v_nextDeclIdx_420_);
lean_dec(v_toGoalState_415_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_450_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc(v_head_409_);
v___x_441_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_421_, v_congrTable_424_, v_head_409_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_nextDeclIdx_420_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_enodeMap_421_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_exprs_422_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_parents_423_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_appMap_425_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_indicesFound_426_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_toProcess_427_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_nextIdx_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 9, v_newRawFacts_430_);
lean_ctor_set(v_reuseFailAlloc_449_, 10, v_facts_431_);
lean_ctor_set(v_reuseFailAlloc_449_, 11, v_extThms_432_);
lean_ctor_set(v_reuseFailAlloc_449_, 12, v_ematch_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 13, v_inj_434_);
lean_ctor_set(v_reuseFailAlloc_449_, 14, v_split_435_);
lean_ctor_set(v_reuseFailAlloc_449_, 15, v_clean_436_);
lean_ctor_set(v_reuseFailAlloc_449_, 16, v_sstates_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_449_, sizeof(void*)*17, v_inconsistent_428_);
v___x_443_ = v_reuseFailAlloc_449_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_443_);
v___x_445_ = v___x_418_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_mvarId_416_);
v___x_445_ = v_reuseFailAlloc_448_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_st_ref_put(v___y_413_, v___x_445_);
v_as_x27_395_ = v_tail_410_;
v_b_396_ = v___x_411_;
goto _start;
}
}
}
}
}
v___jp_452_:
{
if (v_a_453_ == 0)
{
v_as_x27_395_ = v_tail_410_;
v_b_396_ = v___x_411_;
goto _start;
}
else
{
lean_object* v_toCold_455_; lean_object* v_options_456_; uint8_t v_hasTrace_457_; 
v_toCold_455_ = lean_ctor_get(v___y_405_, 0);
v_options_456_ = lean_ctor_get(v_toCold_455_, 2);
v_hasTrace_457_ = lean_ctor_get_uint8(v_options_456_, sizeof(void*)*1);
if (v_hasTrace_457_ == 0)
{
v___y_413_ = v___y_397_;
goto v___jp_412_;
}
else
{
lean_object* v_inheritedTraceOptions_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_inheritedTraceOptions_458_ = lean_ctor_get(v_toCold_455_, 11);
v___x_459_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_460_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_458_, v_options_456_, v___x_460_);
if (v___x_461_ == 0)
{
v___y_413_ = v___y_397_;
goto v___jp_412_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_updateLastTag(v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref_known(v___x_462_, 1);
v___x_463_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_409_);
v___x_464_ = l_Lean_MessageData_ofExpr(v_head_409_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_459_, v___x_465_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_dec_ref_known(v___x_466_, 1);
v___y_413_ = v___y_397_;
goto v___jp_412_;
}
else
{
return v___x_466_;
}
}
else
{
return v___x_462_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_395_ = stack[0].m_obj;
lean_object* v_b_396_ = stack[1].m_obj;
lean_object* v___y_397_ = stack[2].m_obj;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v___y_399_ = stack[4].m_obj;
lean_object* v___y_400_ = stack[5].m_obj;
lean_object* v___y_401_ = stack[6].m_obj;
lean_object* v___y_402_ = stack[7].m_obj;
lean_object* v___y_403_ = stack[8].m_obj;
lean_object* v___y_404_ = stack[9].m_obj;
lean_object* v___y_405_ = stack[10].m_obj;
lean_object* v___y_406_ = stack[11].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_395_, v_b_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_480_, v_b_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec(v___y_482_);
lean_dec(v_as_x27_480_);
return v_res_493_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_Grind_getParents___redArg(v_root_494_, v_a_495_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_507_);
v___x_509_ = lean_box(0);
v___x_510_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_508_, v___x_509_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v___x_508_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_510_, 0);
lean_dec(v_unused_518_);
v___x_512_ = v___x_510_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_dec(v___x_510_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_a_507_);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_507_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_507_);
v_a_519_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_510_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_510_);
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
else
{
return v___x_506_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_494_ = stack[0].m_obj;
lean_object* v_a_495_ = stack[1].m_obj;
lean_object* v_a_496_ = stack[2].m_obj;
lean_object* v_a_497_ = stack[3].m_obj;
lean_object* v_a_498_ = stack[4].m_obj;
lean_object* v_a_499_ = stack[5].m_obj;
lean_object* v_a_500_ = stack[6].m_obj;
lean_object* v_a_501_ = stack[7].m_obj;
lean_object* v_a_502_ = stack[8].m_obj;
lean_object* v_a_503_ = stack[9].m_obj;
lean_object* v_a_504_ = stack[10].m_obj;
lean_object* v_res_527_;
v_res_527_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
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
lean_dec_ref(v_root_528_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_541_, lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_541_, v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_546_, lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_546_, v_00_u03b2_547_, v_x_548_, v_x_549_);
lean_dec_ref(v___x_546_);
return v_res_550_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_551_, v_msg_552_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_564_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_551_ = stack[0].m_obj;
lean_object* v_msg_552_ = stack[1].m_obj;
lean_object* v___y_553_ = stack[2].m_obj;
lean_object* v___y_554_ = stack[3].m_obj;
lean_object* v___y_555_ = stack[4].m_obj;
lean_object* v___y_556_ = stack[5].m_obj;
lean_object* v___y_557_ = stack[6].m_obj;
lean_object* v___y_558_ = stack[7].m_obj;
lean_object* v___y_559_ = stack[8].m_obj;
lean_object* v___y_560_ = stack[9].m_obj;
lean_object* v___y_561_ = stack[10].m_obj;
lean_object* v___y_562_ = stack[11].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_551_, v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_566_, v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec(v___y_568_);
return v_res_579_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_580_, lean_object* v_as_x27_581_, lean_object* v_b_582_, lean_object* v_a_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_581_, v_b_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_595_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_580_ = stack[0].m_obj;
lean_object* v_as_x27_581_ = stack[1].m_obj;
lean_object* v_b_582_ = stack[2].m_obj;
lean_object* v___y_584_ = stack[4].m_obj;
lean_object* v___y_585_ = stack[5].m_obj;
lean_object* v___y_586_ = stack[6].m_obj;
lean_object* v___y_587_ = stack[7].m_obj;
lean_object* v___y_588_ = stack[8].m_obj;
lean_object* v___y_589_ = stack[9].m_obj;
lean_object* v___y_590_ = stack[10].m_obj;
lean_object* v___y_591_ = stack[11].m_obj;
lean_object* v___y_592_ = stack[12].m_obj;
lean_object* v___y_593_ = stack[13].m_obj;
lean_object* v_res_596_;
v_res_596_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_580_, v_as_x27_581_, v_b_582_, lean_box(0), v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_597_, lean_object* v_as_x27_598_, lean_object* v_b_599_, lean_object* v_a_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_597_, v_as_x27_598_, v_b_599_, v_a_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v_as_x27_598_);
lean_dec(v_as_597_);
return v_res_612_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_613_, lean_object* v_00_u03b2_614_, lean_object* v_x_615_, size_t v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_613_, v_x_615_, v_x_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_613_ = stack[0].m_obj;
lean_object* v_x_615_ = stack[2].m_obj;
size_t v_x_616_ = stack[3].m_num;
lean_object* v_x_617_ = stack[4].m_obj;
lean_object* v_res_619_;
v_res_619_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_613_, lean_box(0), v_x_615_, v_x_616_, v_x_617_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_620_, lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_23426__boxed_625_; lean_object* v_res_626_; 
v_x_23426__boxed_625_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_res_626_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_620_, v_00_u03b2_621_, v_x_622_, v_x_23426__boxed_625_, v_x_624_);
lean_dec_ref(v___x_620_);
return v_res_626_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
if (lean_obj_tag(v_as_x27_630_) == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_631_);
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v___x_646_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; uint8_t v_a_661_; uint8_t v___x_675_; 
v_head_644_ = lean_ctor_get(v_as_x27_630_, 0);
v_tail_645_ = lean_ctor_get(v_as_x27_630_, 1);
v___x_646_ = lean_box(0);
v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_644_);
if (v___x_675_ == 0)
{
v_a_661_ = v___x_675_;
goto v___jp_660_;
}
else
{
lean_object* v___x_676_; 
lean_inc(v_head_644_);
v___x_676_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_644_, v___y_632_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; uint8_t v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = lean_unbox(v_a_677_);
lean_dec(v_a_677_);
v_a_661_ = v___x_678_;
goto v___jp_660_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_676_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
v___jp_647_:
{
lean_object* v___x_658_; 
lean_inc(v_head_644_);
v___x_658_ = l_Lean_Meta_Grind_addCongrTable(v_head_644_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec_ref_known(v___x_658_, 1);
v_as_x27_630_ = v_tail_645_;
v_b_631_ = v___x_646_;
goto _start;
}
else
{
return v___x_658_;
}
}
v___jp_660_:
{
if (v_a_661_ == 0)
{
v_as_x27_630_ = v_tail_645_;
v_b_631_ = v___x_646_;
goto _start;
}
else
{
lean_object* v_toCold_663_; lean_object* v_options_664_; uint8_t v_hasTrace_665_; 
v_toCold_663_ = lean_ctor_get(v___y_640_, 0);
v_options_664_ = lean_ctor_get(v_toCold_663_, 2);
v_hasTrace_665_ = lean_ctor_get_uint8(v_options_664_, sizeof(void*)*1);
if (v_hasTrace_665_ == 0)
{
v___y_648_ = v___y_632_;
v___y_649_ = v___y_633_;
v___y_650_ = v___y_634_;
v___y_651_ = v___y_635_;
v___y_652_ = v___y_636_;
v___y_653_ = v___y_637_;
v___y_654_ = v___y_638_;
v___y_655_ = v___y_639_;
v___y_656_ = v___y_640_;
v___y_657_ = v___y_641_;
goto v___jp_647_;
}
else
{
lean_object* v_inheritedTraceOptions_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_inheritedTraceOptions_666_ = lean_ctor_get(v_toCold_663_, 11);
v___x_667_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_668_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_666_, v_options_664_, v___x_668_);
if (v___x_669_ == 0)
{
v___y_648_ = v___y_632_;
v___y_649_ = v___y_633_;
v___y_650_ = v___y_634_;
v___y_651_ = v___y_635_;
v___y_652_ = v___y_636_;
v___y_653_ = v___y_637_;
v___y_654_ = v___y_638_;
v___y_655_ = v___y_639_;
v___y_656_ = v___y_640_;
v___y_657_ = v___y_641_;
goto v___jp_647_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Grind_updateLastTag(v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref_known(v___x_670_, 1);
v___x_671_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_644_);
v___x_672_ = l_Lean_MessageData_ofExpr(v_head_644_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_667_, v___x_673_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_dec_ref_known(v___x_674_, 1);
v___y_648_ = v___y_632_;
v___y_649_ = v___y_633_;
v___y_650_ = v___y_634_;
v___y_651_ = v___y_635_;
v___y_652_ = v___y_636_;
v___y_653_ = v___y_637_;
v___y_654_ = v___y_638_;
v___y_655_ = v___y_639_;
v___y_656_ = v___y_640_;
v___y_657_ = v___y_641_;
goto v___jp_647_;
}
else
{
return v___x_674_;
}
}
else
{
return v___x_670_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_630_ = stack[0].m_obj;
lean_object* v_b_631_ = stack[1].m_obj;
lean_object* v___y_632_ = stack[2].m_obj;
lean_object* v___y_633_ = stack[3].m_obj;
lean_object* v___y_634_ = stack[4].m_obj;
lean_object* v___y_635_ = stack[5].m_obj;
lean_object* v___y_636_ = stack[6].m_obj;
lean_object* v___y_637_ = stack[7].m_obj;
lean_object* v___y_638_ = stack[8].m_obj;
lean_object* v___y_639_ = stack[9].m_obj;
lean_object* v___y_640_ = stack[10].m_obj;
lean_object* v___y_641_ = stack[11].m_obj;
lean_object* v_res_687_;
v_res_687_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_630_, v_b_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_688_, lean_object* v_b_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_688_, v_b_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v_as_x27_688_);
return v_res_701_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_702_);
v___x_715_ = lean_box(0);
v___x_716_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_714_, v___x_715_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v___x_714_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_724_);
v___x_718_ = v___x_716_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_715_);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_715_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
return v___x_716_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_0interp(lean_interpreter_value* stack)
{
lean_object* v_parents_702_ = stack[0].m_obj;
lean_object* v_a_703_ = stack[1].m_obj;
lean_object* v_a_704_ = stack[2].m_obj;
lean_object* v_a_705_ = stack[3].m_obj;
lean_object* v_a_706_ = stack[4].m_obj;
lean_object* v_a_707_ = stack[5].m_obj;
lean_object* v_a_708_ = stack[6].m_obj;
lean_object* v_a_709_ = stack[7].m_obj;
lean_object* v_a_710_ = stack[8].m_obj;
lean_object* v_a_711_ = stack[9].m_obj;
lean_object* v_a_712_ = stack[10].m_obj;
lean_object* v_res_725_;
v_res_725_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec(v_parents_726_);
return v_res_738_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_739_, lean_object* v_as_x27_740_, lean_object* v_b_741_, lean_object* v_a_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_740_, v_b_741_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_739_ = stack[0].m_obj;
lean_object* v_as_x27_740_ = stack[1].m_obj;
lean_object* v_b_741_ = stack[2].m_obj;
lean_object* v___y_743_ = stack[4].m_obj;
lean_object* v___y_744_ = stack[5].m_obj;
lean_object* v___y_745_ = stack[6].m_obj;
lean_object* v___y_746_ = stack[7].m_obj;
lean_object* v___y_747_ = stack[8].m_obj;
lean_object* v___y_748_ = stack[9].m_obj;
lean_object* v___y_749_ = stack[10].m_obj;
lean_object* v___y_750_ = stack[11].m_obj;
lean_object* v___y_751_ = stack[12].m_obj;
lean_object* v___y_752_ = stack[13].m_obj;
lean_object* v_res_755_;
v_res_755_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_739_, v_as_x27_740_, v_b_741_, lean_box(0), v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_756_, lean_object* v_as_x27_757_, lean_object* v_b_758_, lean_object* v_a_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_756_, v_as_x27_757_, v_b_758_, v_a_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v_as_x27_757_);
lean_dec(v_as_756_);
return v_res_771_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_array_get_size(v_keys_772_);
v___x_776_ = lean_nat_dec_lt(v_i_773_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_i_773_);
return v___x_776_;
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_keys_772_, v_i_773_);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_k_774_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_i_773_, v___x_779_);
lean_dec(v_i_773_);
v_i_773_ = v___x_780_;
goto _start;
}
else
{
lean_dec(v_i_773_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_772_ = stack[0].m_obj;
lean_object* v_i_773_ = stack[1].m_obj;
lean_object* v_k_774_ = stack[2].m_obj;
uint8_t v_res_782_;
v_res_782_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_772_, v_i_773_, v_k_774_);
stack->m_num = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_783_, lean_object* v_i_784_, lean_object* v_k_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_783_, v_i_784_, v_k_785_);
lean_dec(v_k_785_);
lean_dec_ref(v_keys_783_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_788_, size_t v_x_789_, lean_object* v_x_790_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v_es_791_; lean_object* v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v_j_795_; lean_object* v___x_796_; 
v_es_791_ = lean_ctor_get(v_x_788_, 0);
v___x_792_ = lean_box(2);
v___x_793_ = ((size_t)31ULL);
v___x_794_ = lean_usize_land(v_x_789_, v___x_793_);
v_j_795_ = lean_usize_to_nat(v___x_794_);
v___x_796_ = lean_array_get_borrowed(v___x_792_, v_es_791_, v_j_795_);
lean_dec(v_j_795_);
switch(lean_obj_tag(v___x_796_))
{
case 0:
{
lean_object* v_key_797_; uint8_t v___x_798_; 
v_key_797_ = lean_ctor_get(v___x_796_, 0);
v___x_798_ = l_Lean_instBEqMVarId_beq(v_x_790_, v_key_797_);
return v___x_798_;
}
case 1:
{
lean_object* v_node_799_; size_t v___x_800_; size_t v___x_801_; 
v_node_799_ = lean_ctor_get(v___x_796_, 0);
v___x_800_ = ((size_t)5ULL);
v___x_801_ = lean_usize_shift_right(v_x_789_, v___x_800_);
v_x_788_ = v_node_799_;
v_x_789_ = v___x_801_;
goto _start;
}
default: 
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
}
else
{
lean_object* v_ks_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_ks_804_ = lean_ctor_get(v_x_788_, 0);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_804_, v___x_805_, v_x_790_);
return v___x_806_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_788_ = stack[0].m_obj;
size_t v_x_789_ = stack[1].m_num;
lean_object* v_x_790_ = stack[2].m_obj;
uint8_t v_res_807_;
v_res_807_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_788_, v_x_789_, v_x_790_);
stack->m_num = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
size_t v_x_9687__boxed_811_; uint8_t v_res_812_; lean_object* v_r_813_; 
v_x_9687__boxed_811_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_res_812_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_808_, v_x_9687__boxed_811_, v_x_810_);
lean_dec(v_x_810_);
lean_dec_ref(v_x_808_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
uint64_t v___x_816_; size_t v___x_817_; uint8_t v___x_818_; 
v___x_816_ = l_Lean_instHashableMVarId_hash(v_x_815_);
v___x_817_ = lean_uint64_to_usize(v___x_816_);
v___x_818_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_814_, v___x_817_, v_x_815_);
return v___x_818_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_814_ = stack[0].m_obj;
lean_object* v_x_815_ = stack[1].m_obj;
uint8_t v_res_819_;
v_res_819_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_814_, v_x_815_);
stack->m_num = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec_ref(v_x_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_mctx_828_; lean_object* v_eAssignment_829_; uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_827_ = lean_st_ref_get(v___y_825_);
v_mctx_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_mctx_828_);
lean_dec(v___x_827_);
v_eAssignment_829_ = lean_ctor_get(v_mctx_828_, 8);
lean_inc_ref(v_eAssignment_829_);
lean_dec_ref(v_mctx_828_);
v___x_830_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_829_, v_mvarId_824_);
lean_dec_ref(v_eAssignment_829_);
v___x_831_ = lean_box(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_824_ = stack[0].m_obj;
lean_object* v___y_825_ = stack[1].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_824_, v___y_825_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v_mvarId_834_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_848_ = l_Lean_mkConst(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_box(0);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_856_ = l_Lean_mkConst(v___x_855_, v___x_854_);
return v___x_856_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_mvarId_869_; lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_924_; 
v___x_868_ = lean_st_ref_get(v_a_857_);
v_mvarId_869_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_mvarId_869_);
lean_dec(v___x_868_);
v___x_870_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_869_, v_a_864_);
lean_dec(v_mvarId_869_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_924_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_del_object(v___x_873_);
v___x_876_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_861_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_877_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_861_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_861_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_886_ = l_Lean_mkApp4(v___x_884_, v_a_881_, v_a_883_, v_a_879_, v___x_885_);
v___x_887_ = l_Lean_Meta_Grind_closeGoal(v___x_886_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_887_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_881_);
lean_dec(v_a_879_);
v_a_888_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_882_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_882_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_a_879_);
v_a_896_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_880_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_880_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_878_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_878_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_876_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_876_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_920_);
v___x_922_ = v___x_873_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_857_ = stack[0].m_obj;
lean_object* v_a_858_ = stack[1].m_obj;
lean_object* v_a_859_ = stack[2].m_obj;
lean_object* v_a_860_ = stack[3].m_obj;
lean_object* v_a_861_ = stack[4].m_obj;
lean_object* v_a_862_ = stack[5].m_obj;
lean_object* v_a_863_ = stack[6].m_obj;
lean_object* v_a_864_ = stack[7].m_obj;
lean_object* v_a_865_ = stack[8].m_obj;
lean_object* v_a_866_ = stack[9].m_obj;
lean_object* v_res_925_;
v_res_925_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec(v_a_926_);
return v_res_937_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_938_, v___y_946_);
return v___x_950_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_938_ = stack[0].m_obj;
lean_object* v___y_939_ = stack[1].m_obj;
lean_object* v___y_940_ = stack[2].m_obj;
lean_object* v___y_941_ = stack[3].m_obj;
lean_object* v___y_942_ = stack[4].m_obj;
lean_object* v___y_943_ = stack[5].m_obj;
lean_object* v___y_944_ = stack[6].m_obj;
lean_object* v___y_945_ = stack[7].m_obj;
lean_object* v___y_946_ = stack[8].m_obj;
lean_object* v___y_947_ = stack[9].m_obj;
lean_object* v___y_948_ = stack[10].m_obj;
lean_object* v_res_951_;
v_res_951_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v_mvarId_952_);
return v_res_964_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_966_, v_x_967_);
return v___x_968_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_966_ = stack[1].m_obj;
lean_object* v_x_967_ = stack[2].m_obj;
uint8_t v_res_969_;
v_res_969_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_box(0), v_x_966_, v_x_967_);
stack->m_num = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
uint8_t v_res_973_; lean_object* v_r_974_; 
v_res_973_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_970_, v_x_971_, v_x_972_);
lean_dec(v_x_972_);
lean_dec_ref(v_x_971_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, size_t v_x_977_, lean_object* v_x_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_976_, v_x_977_, v_x_978_);
return v___x_979_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_976_ = stack[1].m_obj;
size_t v_x_977_ = stack[2].m_num;
lean_object* v_x_978_ = stack[3].m_obj;
uint8_t v_res_980_;
v_res_980_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_box(0), v_x_976_, v_x_977_, v_x_978_);
stack->m_num = v_res_980_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
size_t v_x_10111__boxed_985_; uint8_t v_res_986_; lean_object* v_r_987_; 
v_x_10111__boxed_985_ = lean_unbox_usize(v_x_983_);
lean_dec(v_x_983_);
v_res_986_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_981_, v_x_982_, v_x_10111__boxed_985_, v_x_984_);
lean_dec(v_x_984_);
lean_dec_ref(v_x_982_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_988_, lean_object* v_keys_989_, lean_object* v_vals_990_, lean_object* v_heq_991_, lean_object* v_i_992_, lean_object* v_k_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_989_, v_i_992_, v_k_993_);
return v___x_994_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_989_ = stack[1].m_obj;
lean_object* v_vals_990_ = stack[2].m_obj;
lean_object* v_i_992_ = stack[4].m_obj;
lean_object* v_k_993_ = stack[5].m_obj;
uint8_t v_res_995_;
v_res_995_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_keys_989_, v_vals_990_, lean_box(0), v_i_992_, v_k_993_);
stack->m_num = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_996_, lean_object* v_keys_997_, lean_object* v_vals_998_, lean_object* v_heq_999_, lean_object* v_i_1000_, lean_object* v_k_1001_){
_start:
{
uint8_t v_res_1002_; lean_object* v_r_1003_; 
v_res_1002_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_996_, v_keys_997_, v_vals_998_, v_heq_999_, v_i_1000_, v_k_1001_);
lean_dec(v_k_1001_);
lean_dec_ref(v_vals_998_);
lean_dec_ref(v_keys_997_);
v_r_1003_ = lean_box(v_res_1002_);
return v_r_1003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_1009_ = l_Lean_mkConst(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_1010_, lean_object* v_rhs_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; 
lean_inc_ref(v_rhs_1011_);
lean_inc_ref(v_lhs_1010_);
v___x_1023_ = l_Lean_Meta_mkEq(v_lhs_1010_, v_rhs_1011_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc(v_a_1012_);
v___x_1025_ = lean_grind_mk_eq_proof(v_lhs_1010_, v_rhs_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
lean_inc(v_a_1024_);
v___x_1027_ = l_Lean_Meta_mkDecide(v_a_1024_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1030_ = l_Lean_Expr_appArg_x21(v_a_1028_);
lean_dec(v_a_1028_);
v___x_1031_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_1024_);
v___x_1032_ = l_Lean_mkApp3(v___x_1029_, v_a_1024_, v___x_1030_, v___x_1031_);
v___x_1033_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1016_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1036_ = l_Lean_mkApp4(v___x_1035_, v_a_1024_, v_a_1034_, v___x_1032_, v_a_1026_);
v___x_1037_ = l_Lean_Meta_Grind_closeGoal(v___x_1036_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1037_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___x_1032_);
lean_dec(v_a_1026_);
lean_dec(v_a_1024_);
v_a_1038_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1033_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1033_);
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
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v_a_1026_);
lean_dec(v_a_1024_);
v_a_1046_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1027_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1027_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_a_1024_);
v_a_1054_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1025_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1025_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_rhs_1011_);
lean_dec_ref(v_lhs_1010_);
v_a_1062_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1023_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1023_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1010_ = stack[0].m_obj;
lean_object* v_rhs_1011_ = stack[1].m_obj;
lean_object* v_a_1012_ = stack[2].m_obj;
lean_object* v_a_1013_ = stack[3].m_obj;
lean_object* v_a_1014_ = stack[4].m_obj;
lean_object* v_a_1015_ = stack[5].m_obj;
lean_object* v_a_1016_ = stack[6].m_obj;
lean_object* v_a_1017_ = stack[7].m_obj;
lean_object* v_a_1018_ = stack[8].m_obj;
lean_object* v_a_1019_ = stack[9].m_obj;
lean_object* v_a_1020_ = stack[10].m_obj;
lean_object* v_a_1021_ = stack[11].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1010_, v_rhs_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1071_, lean_object* v_rhs_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1071_, v_rhs_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
return v_res_1084_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1085_, lean_object* v_as_x27_1086_, lean_object* v_b_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
if (lean_obj_tag(v_as_x27_1086_) == 0)
{
lean_object* v___x_1099_; 
lean_dec(v___x_1085_);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_b_1087_);
return v___x_1099_;
}
else
{
lean_object* v_head_1100_; lean_object* v_tail_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_head_1100_ = lean_ctor_get(v_as_x27_1086_, 0);
v_tail_1101_ = lean_ctor_get(v_as_x27_1086_, 1);
v___x_1102_ = lean_box(0);
v___x_1103_ = lean_st_ref_get(v___y_1088_);
lean_inc(v_head_1100_);
v___x_1104_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1103_, v_head_1100_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___x_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v_self_1106_; lean_object* v_next_1107_; lean_object* v_root_1108_; lean_object* v_congr_1109_; lean_object* v_target_x3f_1110_; lean_object* v_proof_x3f_1111_; uint8_t v_flipped_1112_; lean_object* v_size_1113_; uint8_t v_interpreted_1114_; uint8_t v_ctor_1115_; uint8_t v_hasLambdas_1116_; uint8_t v_heqProofs_1117_; lean_object* v_idx_1118_; lean_object* v_generation_1119_; lean_object* v_mt_1120_; lean_object* v_sTerms_1121_; uint8_t v_funCC_1122_; lean_object* v_ematchDiagSource_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1135_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v_self_1106_ = lean_ctor_get(v_a_1105_, 0);
v_next_1107_ = lean_ctor_get(v_a_1105_, 1);
v_root_1108_ = lean_ctor_get(v_a_1105_, 2);
v_congr_1109_ = lean_ctor_get(v_a_1105_, 3);
v_target_x3f_1110_ = lean_ctor_get(v_a_1105_, 4);
v_proof_x3f_1111_ = lean_ctor_get(v_a_1105_, 5);
v_flipped_1112_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12);
v_size_1113_ = lean_ctor_get(v_a_1105_, 6);
v_interpreted_1114_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12 + 1);
v_ctor_1115_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12 + 2);
v_hasLambdas_1116_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12 + 3);
v_heqProofs_1117_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12 + 4);
v_idx_1118_ = lean_ctor_get(v_a_1105_, 7);
v_generation_1119_ = lean_ctor_get(v_a_1105_, 8);
v_mt_1120_ = lean_ctor_get(v_a_1105_, 9);
v_sTerms_1121_ = lean_ctor_get(v_a_1105_, 10);
v_funCC_1122_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1123_ = lean_ctor_get(v_a_1105_, 11);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1105_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1125_ = v_a_1105_;
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_ematchDiagSource_1123_);
lean_inc(v_sTerms_1121_);
lean_inc(v_mt_1120_);
lean_inc(v_generation_1119_);
lean_inc(v_idx_1118_);
lean_inc(v_size_1113_);
lean_inc(v_proof_x3f_1111_);
lean_inc(v_target_x3f_1110_);
lean_inc(v_congr_1109_);
lean_inc(v_root_1108_);
lean_inc(v_next_1107_);
lean_inc(v_self_1106_);
lean_dec(v_a_1105_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_lt(v_mt_1120_, v___x_1085_);
lean_dec(v_mt_1120_);
if (v___x_1127_ == 0)
{
lean_del_object(v___x_1125_);
lean_dec(v_ematchDiagSource_1123_);
lean_dec(v_sTerms_1121_);
lean_dec(v_generation_1119_);
lean_dec(v_idx_1118_);
lean_dec(v_size_1113_);
lean_dec(v_proof_x3f_1111_);
lean_dec(v_target_x3f_1110_);
lean_dec_ref(v_congr_1109_);
lean_dec_ref(v_root_1108_);
lean_dec_ref(v_next_1107_);
lean_dec_ref(v_self_1106_);
v_as_x27_1086_ = v_tail_1101_;
v_b_1087_ = v___x_1102_;
goto _start;
}
else
{
lean_object* v___x_1130_; 
lean_inc(v___x_1085_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 9, v___x_1085_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_self_1106_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_next_1107_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_root_1108_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_congr_1109_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_target_x3f_1110_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_proof_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1134_, 6, v_size_1113_);
lean_ctor_set(v_reuseFailAlloc_1134_, 7, v_idx_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 8, v_generation_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 9, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1134_, 10, v_sTerms_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 11, v_ematchDiagSource_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12, v_flipped_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12 + 1, v_interpreted_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12 + 2, v_ctor_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12 + 3, v_hasLambdas_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12 + 4, v_heqProofs_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*12 + 5, v_funCC_1122_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; 
lean_inc(v_head_1100_);
v___x_1131_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1100_, v___x_1130_, v___y_1088_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1131_, 1);
v___x_1132_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1100_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_dec_ref_known(v___x_1132_, 1);
v_as_x27_1086_ = v_tail_1101_;
v_b_1087_ = v___x_1102_;
goto _start;
}
else
{
lean_dec(v___x_1085_);
return v___x_1132_;
}
}
else
{
lean_dec(v___x_1085_);
return v___x_1131_;
}
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v___x_1085_);
v_a_1136_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1104_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1104_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1085_ = stack[0].m_obj;
lean_object* v_as_x27_1086_ = stack[1].m_obj;
lean_object* v_b_1087_ = stack[2].m_obj;
lean_object* v___y_1088_ = stack[3].m_obj;
lean_object* v___y_1089_ = stack[4].m_obj;
lean_object* v___y_1090_ = stack[5].m_obj;
lean_object* v___y_1091_ = stack[6].m_obj;
lean_object* v___y_1092_ = stack[7].m_obj;
lean_object* v___y_1093_ = stack[8].m_obj;
lean_object* v___y_1094_ = stack[9].m_obj;
lean_object* v___y_1095_ = stack[10].m_obj;
lean_object* v___y_1096_ = stack[11].m_obj;
lean_object* v___y_1097_ = stack[12].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1085_, v_as_x27_1086_, v_b_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
stack->m_obj
 = v_res_1144_;
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v_toGoalState_1158_; lean_object* v_ematch_1159_; lean_object* v_gmt_1160_; lean_object* v___x_1161_; 
v___x_1157_ = lean_st_ref_get(v_a_1146_);
v_toGoalState_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc_ref(v_toGoalState_1158_);
lean_dec(v___x_1157_);
v_ematch_1159_ = lean_ctor_get(v_toGoalState_1158_, 12);
lean_inc_ref(v_ematch_1159_);
lean_dec_ref(v_toGoalState_1158_);
v_gmt_1160_ = lean_ctor_get(v_ematch_1159_, 1);
lean_inc(v_gmt_1160_);
lean_dec_ref(v_ematch_1159_);
v___x_1161_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1145_, v_a_1146_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1162_);
lean_dec(v_a_1162_);
v___x_1164_ = lean_box(0);
v___x_1165_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1160_, v___x_1163_, v___x_1164_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v___x_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1165_, 0);
lean_dec(v_unused_1173_);
v___x_1167_ = v___x_1165_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_dec(v___x_1165_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1164_);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1164_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
return v___x_1165_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_gmt_1160_);
v_a_1174_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1161_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1161_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_1145_ = stack[0].m_obj;
lean_object* v_a_1146_ = stack[1].m_obj;
lean_object* v_a_1147_ = stack[2].m_obj;
lean_object* v_a_1148_ = stack[3].m_obj;
lean_object* v_a_1149_ = stack[4].m_obj;
lean_object* v_a_1150_ = stack[5].m_obj;
lean_object* v_a_1151_ = stack[6].m_obj;
lean_object* v_a_1152_ = stack[7].m_obj;
lean_object* v_a_1153_ = stack[8].m_obj;
lean_object* v_a_1154_ = stack[9].m_obj;
lean_object* v_a_1155_ = stack[10].m_obj;
lean_object* v_res_1182_;
v_res_1182_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_root_1183_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1196_, lean_object* v_as_x27_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1196_, v_as_x27_1197_, v_b_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v_as_x27_1197_);
return v_res_1210_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1211_, lean_object* v_as_1212_, lean_object* v_as_x27_1213_, lean_object* v_b_1214_, lean_object* v_a_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1211_, v_as_x27_1213_, v_b_1214_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1211_ = stack[0].m_obj;
lean_object* v_as_1212_ = stack[1].m_obj;
lean_object* v_as_x27_1213_ = stack[2].m_obj;
lean_object* v_b_1214_ = stack[3].m_obj;
lean_object* v___y_1216_ = stack[5].m_obj;
lean_object* v___y_1217_ = stack[6].m_obj;
lean_object* v___y_1218_ = stack[7].m_obj;
lean_object* v___y_1219_ = stack[8].m_obj;
lean_object* v___y_1220_ = stack[9].m_obj;
lean_object* v___y_1221_ = stack[10].m_obj;
lean_object* v___y_1222_ = stack[11].m_obj;
lean_object* v___y_1223_ = stack[12].m_obj;
lean_object* v___y_1224_ = stack[13].m_obj;
lean_object* v___y_1225_ = stack[14].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1211_, v_as_1212_, v_as_x27_1213_, v_b_1214_, lean_box(0), v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1229_, lean_object* v_as_1230_, lean_object* v_as_x27_1231_, lean_object* v_b_1232_, lean_object* v_a_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1229_, v_as_1230_, v_as_x27_1231_, v_b_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v_as_x27_1231_);
lean_dec(v_as_1230_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = l_List_reverse___redArg(v_a_1247_);
return v___x_1248_;
}
else
{
lean_object* v_head_1249_; lean_object* v_tail_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v_head_1249_ = lean_ctor_get(v_a_1246_, 0);
v_tail_1250_ = lean_ctor_get(v_a_1246_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1252_ = v_a_1246_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_tail_1250_);
lean_inc(v_head_1249_);
lean_dec(v_a_1246_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Lean_MessageData_ofExpr(v_head_1249_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v_a_1247_);
lean_ctor_set(v___x_1252_, 0, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_a_1247_);
v___x_1256_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
v_a_1246_ = v_tail_1250_;
v_a_1247_ = v___x_1256_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1260_, lean_object* v_a_1261_, lean_object* v_fst_1262_, lean_object* v_a_1263_, lean_object* v_lams_1264_, lean_object* v_____r_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1260_, v_a_1263_, v___y_1266_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
if (v___x_1316_ == 0)
{
goto v___jp_1277_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_inc(v_fst_1262_);
v___x_1317_ = l_Array_reverse___redArg(v_fst_1262_);
lean_inc(v_snd_1260_);
v___x_1318_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1264_, v_snd_1260_, v___x_1317_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_dec_ref_known(v___x_1318_, 1);
goto v___jp_1277_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_fst_1262_);
lean_dec(v_snd_1260_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_fst_1262_);
lean_dec(v_snd_1260_);
v_a_1327_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1314_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1314_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
v___jp_1277_:
{
if (lean_obj_tag(v_snd_1260_) == 5)
{
lean_object* v_fn_1278_; lean_object* v_arg_1279_; lean_object* v___x_1280_; 
v_fn_1278_ = lean_ctor_get(v_snd_1260_, 0);
lean_inc_ref(v_fn_1278_);
v_arg_1279_ = lean_ctor_get(v_snd_1260_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1280_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1261_, v___y_1266_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_box(0);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1283_ = lean_grind_internalize(v_snd_1260_, v_a_1281_, v___x_1282_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1293_; 
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1283_, 0);
lean_dec(v_unused_1294_);
v___x_1285_ = v___x_1283_;
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
else
{
lean_dec(v___x_1283_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1287_ = lean_array_push(v_fst_1262_, v_arg_1279_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v_fn_1278_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1289_);
v___x_1291_ = v___x_1285_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_fn_1278_);
lean_dec(v_fst_1262_);
v_a_1295_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1283_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1283_);
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
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref_known(v_snd_1260_, 2);
lean_dec_ref(v_fn_1278_);
lean_dec(v_fst_1262_);
v_a_1303_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1280_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1280_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_fst_1262_);
lean_ctor_set(v___x_1311_, 1, v_snd_1260_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1260_ = stack[0].m_obj;
lean_object* v_a_1261_ = stack[1].m_obj;
lean_object* v_fst_1262_ = stack[2].m_obj;
lean_object* v_a_1263_ = stack[3].m_obj;
lean_object* v_lams_1264_ = stack[4].m_obj;
lean_object* v_____r_1265_ = stack[5].m_obj;
lean_object* v___y_1266_ = stack[6].m_obj;
lean_object* v___y_1267_ = stack[7].m_obj;
lean_object* v___y_1268_ = stack[8].m_obj;
lean_object* v___y_1269_ = stack[9].m_obj;
lean_object* v___y_1270_ = stack[10].m_obj;
lean_object* v___y_1271_ = stack[11].m_obj;
lean_object* v___y_1272_ = stack[12].m_obj;
lean_object* v___y_1273_ = stack[13].m_obj;
lean_object* v___y_1274_ = stack[14].m_obj;
lean_object* v___y_1275_ = stack[15].m_obj;
lean_object* v_res_1335_;
v_res_1335_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1260_, v_a_1261_, v_fst_1262_, v_a_1263_, v_lams_1264_, v_____r_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1336_ = _args[0];
lean_object* v_a_1337_ = _args[1];
lean_object* v_fst_1338_ = _args[2];
lean_object* v_a_1339_ = _args[3];
lean_object* v_lams_1340_ = _args[4];
lean_object* v_____r_1341_ = _args[5];
lean_object* v___y_1342_ = _args[6];
lean_object* v___y_1343_ = _args[7];
lean_object* v___y_1344_ = _args[8];
lean_object* v___y_1345_ = _args[9];
lean_object* v___y_1346_ = _args[10];
lean_object* v___y_1347_ = _args[11];
lean_object* v___y_1348_ = _args[12];
lean_object* v___y_1349_ = _args[13];
lean_object* v___y_1350_ = _args[14];
lean_object* v___y_1351_ = _args[15];
lean_object* v___y_1352_ = _args[16];
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1336_, v_a_1337_, v_fst_1338_, v_a_1339_, v_lams_1340_, v_____r_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v_lams_1340_);
lean_dec_ref(v_a_1339_);
lean_dec_ref(v_a_1337_);
return v_res_1353_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1360_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1361_ = l_Lean_Name_append(v___x_1360_, v___x_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_lams_1367_, lean_object* v_a_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___y_1381_; lean_object* v_toCold_1401_; lean_object* v_options_1402_; lean_object* v_fst_1403_; lean_object* v_snd_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1441_; 
v_toCold_1401_ = lean_ctor_get(v___y_1377_, 0);
v_options_1402_ = lean_ctor_get(v_toCold_1401_, 2);
v_fst_1403_ = lean_ctor_get(v_a_1368_, 0);
v_snd_1404_ = lean_ctor_get(v_a_1368_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_a_1368_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1406_ = v_a_1368_;
v_isShared_1407_ = v_isSharedCheck_1441_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1404_);
lean_inc(v_fst_1403_);
lean_dec(v_a_1368_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1441_;
goto v_resetjp_1405_;
}
v___jp_1380_:
{
if (lean_obj_tag(v___y_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1392_; 
v_a_1382_ = lean_ctor_get(v___y_1381_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___y_1381_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1384_ = v___y_1381_;
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___y_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1392_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
if (lean_obj_tag(v_a_1382_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; 
v_a_1386_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v_a_1382_, 1);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_a_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
lean_object* v_a_1390_; 
lean_del_object(v___x_1384_);
v_a_1390_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v_a_1382_, 1);
v_a_1368_ = v_a_1390_;
goto _start;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___y_1381_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___y_1381_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___y_1381_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___y_1381_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
v_resetjp_1405_:
{
lean_object* v_inheritedTraceOptions_1408_; uint8_t v_hasTrace_1409_; 
v_inheritedTraceOptions_1408_ = lean_ctor_get(v_toCold_1401_, 11);
v_hasTrace_1409_ = lean_ctor_get_uint8(v_options_1402_, sizeof(void*)*1);
if (v_hasTrace_1409_ == 0)
{
lean_del_object(v___x_1406_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1414_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1408_, v_options_1402_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_del_object(v___x_1406_);
goto v___jp_1410_;
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_Meta_Grind_updateLastTag(v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_dec_ref_known(v___x_1416_, 1);
v___x_1417_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1404_);
v___x_1418_ = l_Lean_MessageData_ofExpr(v_snd_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 7);
lean_ctor_set(v___x_1406_, 1, v___x_1418_);
lean_ctor_set(v___x_1406_, 0, v___x_1417_);
v___x_1420_ = v___x_1406_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1413_, v___x_1420_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1404_, v_a_1365_, v_fst_1403_, v_a_1366_, v_lams_1367_, v_a_1422_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
v___y_1381_ = v___x_1423_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
v_a_1424_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1421_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1421_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_del_object(v___x_1406_);
lean_dec(v_snd_1404_);
lean_dec(v_fst_1403_);
v_a_1433_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1416_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1416_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
v___jp_1410_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1404_, v_a_1365_, v_fst_1403_, v_a_1366_, v_lams_1367_, v___x_1411_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
v___y_1381_ = v___x_1412_;
goto v___jp_1380_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1365_ = stack[0].m_obj;
lean_object* v_a_1366_ = stack[1].m_obj;
lean_object* v_lams_1367_ = stack[2].m_obj;
lean_object* v_a_1368_ = stack[3].m_obj;
lean_object* v___y_1369_ = stack[4].m_obj;
lean_object* v___y_1370_ = stack[5].m_obj;
lean_object* v___y_1371_ = stack[6].m_obj;
lean_object* v___y_1372_ = stack[7].m_obj;
lean_object* v___y_1373_ = stack[8].m_obj;
lean_object* v___y_1374_ = stack[9].m_obj;
lean_object* v___y_1375_ = stack[10].m_obj;
lean_object* v___y_1376_ = stack[11].m_obj;
lean_object* v___y_1377_ = stack[12].m_obj;
lean_object* v___y_1378_ = stack[13].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1365_, v_a_1366_, v_lams_1367_, v_a_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
stack->m_obj
 = v_res_1442_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_lams_1445_, lean_object* v_a_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1443_, v_a_1444_, v_lams_1445_, v_a_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v_lams_1445_);
lean_dec_ref(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1458_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1464_, lean_object* v_lams_1465_, lean_object* v_as_x27_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
if (lean_obj_tag(v_as_x27_1466_) == 0)
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_b_1467_);
return v___x_1479_;
}
else
{
lean_object* v_toCold_1480_; lean_object* v_options_1481_; lean_object* v_head_1482_; lean_object* v_tail_1483_; lean_object* v_inheritedTraceOptions_1484_; uint8_t v_hasTrace_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; 
v_toCold_1480_ = lean_ctor_get(v___y_1476_, 0);
v_options_1481_ = lean_ctor_get(v_toCold_1480_, 2);
v_head_1482_ = lean_ctor_get(v_as_x27_1466_, 0);
v_tail_1483_ = lean_ctor_get(v_as_x27_1466_, 1);
v_inheritedTraceOptions_1484_ = lean_ctor_get(v_toCold_1480_, 11);
v_hasTrace_1485_ = lean_ctor_get_uint8(v_options_1481_, sizeof(void*)*1);
v___x_1486_ = lean_box(0);
v___x_1487_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1485_ == 0)
{
v___y_1489_ = v___y_1468_;
v___y_1490_ = v___y_1469_;
v___y_1491_ = v___y_1470_;
v___y_1492_ = v___y_1471_;
v___y_1493_ = v___y_1472_;
v___y_1494_ = v___y_1473_;
v___y_1495_ = v___y_1474_;
v___y_1496_ = v___y_1475_;
v___y_1497_ = v___y_1476_;
v___y_1498_ = v___y_1477_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1511_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1484_, v_options_1481_, v___x_1511_);
if (v___x_1512_ == 0)
{
v___y_1489_ = v___y_1468_;
v___y_1490_ = v___y_1469_;
v___y_1491_ = v___y_1470_;
v___y_1492_ = v___y_1471_;
v___y_1493_ = v___y_1472_;
v___y_1494_ = v___y_1473_;
v___y_1495_ = v___y_1474_;
v___y_1496_ = v___y_1475_;
v___y_1497_ = v___y_1476_;
v___y_1498_ = v___y_1477_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_Grind_updateLastTag(v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref_known(v___x_1513_, 1);
v___x_1514_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1482_);
v___x_1515_ = l_Lean_MessageData_ofExpr(v_head_1482_);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1510_, v___x_1516_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec_ref_known(v___x_1517_, 1);
v___y_1489_ = v___y_1468_;
v___y_1490_ = v___y_1469_;
v___y_1491_ = v___y_1470_;
v___y_1492_ = v___y_1471_;
v___y_1493_ = v___y_1472_;
v___y_1494_ = v___y_1473_;
v___y_1495_ = v___y_1474_;
v___y_1496_ = v___y_1475_;
v___y_1497_ = v___y_1476_;
v___y_1498_ = v___y_1477_;
goto v___jp_1488_;
}
else
{
return v___x_1517_;
}
}
else
{
return v___x_1513_;
}
}
}
v___jp_1488_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc(v_head_1482_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1487_);
lean_ctor_set(v___x_1499_, 1, v_head_1482_);
v___x_1500_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1482_, v_a_1464_, v_lams_1465_, v___x_1499_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_dec_ref_known(v___x_1500_, 1);
v_as_x27_1466_ = v_tail_1483_;
v_b_1467_ = v___x_1486_;
goto _start;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1500_);
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
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1464_ = stack[0].m_obj;
lean_object* v_lams_1465_ = stack[1].m_obj;
lean_object* v_as_x27_1466_ = stack[2].m_obj;
lean_object* v_b_1467_ = stack[3].m_obj;
lean_object* v___y_1468_ = stack[4].m_obj;
lean_object* v___y_1469_ = stack[5].m_obj;
lean_object* v___y_1470_ = stack[6].m_obj;
lean_object* v___y_1471_ = stack[7].m_obj;
lean_object* v___y_1472_ = stack[8].m_obj;
lean_object* v___y_1473_ = stack[9].m_obj;
lean_object* v___y_1474_ = stack[10].m_obj;
lean_object* v___y_1475_ = stack[11].m_obj;
lean_object* v___y_1476_ = stack[12].m_obj;
lean_object* v___y_1477_ = stack[13].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1464_, v_lams_1465_, v_as_x27_1466_, v_b_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1519_, lean_object* v_lams_1520_, lean_object* v_as_x27_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1519_, v_lams_1520_, v_as_x27_1521_, v_b_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec(v_as_x27_1521_);
lean_dec_ref(v_lams_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1534_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1535_, lean_object* v_lams_1536_, lean_object* v_as_1537_, lean_object* v_as_x27_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
if (lean_obj_tag(v_as_x27_1538_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_b_1539_);
return v___x_1551_;
}
else
{
lean_object* v_toCold_1552_; lean_object* v_options_1553_; lean_object* v_head_1554_; lean_object* v_tail_1555_; lean_object* v_inheritedTraceOptions_1556_; uint8_t v_hasTrace_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; 
v_toCold_1552_ = lean_ctor_get(v___y_1548_, 0);
v_options_1553_ = lean_ctor_get(v_toCold_1552_, 2);
v_head_1554_ = lean_ctor_get(v_as_x27_1538_, 0);
v_tail_1555_ = lean_ctor_get(v_as_x27_1538_, 1);
v_inheritedTraceOptions_1556_ = lean_ctor_get(v_toCold_1552_, 11);
v_hasTrace_1557_ = lean_ctor_get_uint8(v_options_1553_, sizeof(void*)*1);
v___x_1558_ = lean_box(0);
v___x_1559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1557_ == 0)
{
v___y_1561_ = v___y_1540_;
v___y_1562_ = v___y_1541_;
v___y_1563_ = v___y_1542_;
v___y_1564_ = v___y_1543_;
v___y_1565_ = v___y_1544_;
v___y_1566_ = v___y_1545_;
v___y_1567_ = v___y_1546_;
v___y_1568_ = v___y_1547_;
v___y_1569_ = v___y_1548_;
v___y_1570_ = v___y_1549_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1583_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1584_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1556_, v_options_1553_, v___x_1583_);
if (v___x_1584_ == 0)
{
v___y_1561_ = v___y_1540_;
v___y_1562_ = v___y_1541_;
v___y_1563_ = v___y_1542_;
v___y_1564_ = v___y_1543_;
v___y_1565_ = v___y_1544_;
v___y_1566_ = v___y_1545_;
v___y_1567_ = v___y_1546_;
v___y_1568_ = v___y_1547_;
v___y_1569_ = v___y_1548_;
v___y_1570_ = v___y_1549_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Meta_Grind_updateLastTag(v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1585_, 1);
v___x_1586_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1554_);
v___x_1587_ = l_Lean_MessageData_ofExpr(v_head_1554_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1582_, v___x_1588_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec_ref_known(v___x_1589_, 1);
v___y_1561_ = v___y_1540_;
v___y_1562_ = v___y_1541_;
v___y_1563_ = v___y_1542_;
v___y_1564_ = v___y_1543_;
v___y_1565_ = v___y_1544_;
v___y_1566_ = v___y_1545_;
v___y_1567_ = v___y_1546_;
v___y_1568_ = v___y_1547_;
v___y_1569_ = v___y_1548_;
v___y_1570_ = v___y_1549_;
goto v___jp_1560_;
}
else
{
return v___x_1589_;
}
}
else
{
return v___x_1585_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_inc(v_head_1554_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1559_);
lean_ctor_set(v___x_1571_, 1, v_head_1554_);
v___x_1572_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1554_, v_a_1535_, v_lams_1536_, v___x_1571_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1535_, v_lams_1536_, v_tail_1555_, v___x_1558_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1573_;
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1572_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1535_ = stack[0].m_obj;
lean_object* v_lams_1536_ = stack[1].m_obj;
lean_object* v_as_1537_ = stack[2].m_obj;
lean_object* v_as_x27_1538_ = stack[3].m_obj;
lean_object* v_b_1539_ = stack[4].m_obj;
lean_object* v___y_1540_ = stack[5].m_obj;
lean_object* v___y_1541_ = stack[6].m_obj;
lean_object* v___y_1542_ = stack[7].m_obj;
lean_object* v___y_1543_ = stack[8].m_obj;
lean_object* v___y_1544_ = stack[9].m_obj;
lean_object* v___y_1545_ = stack[10].m_obj;
lean_object* v___y_1546_ = stack[11].m_obj;
lean_object* v___y_1547_ = stack[12].m_obj;
lean_object* v___y_1548_ = stack[13].m_obj;
lean_object* v___y_1549_ = stack[14].m_obj;
lean_object* v_res_1590_;
v_res_1590_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1535_, v_lams_1536_, v_as_1537_, v_as_x27_1538_, v_b_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
stack->m_obj
 = v_res_1590_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1591_, lean_object* v_lams_1592_, lean_object* v_as_1593_, lean_object* v_as_x27_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1591_, v_lams_1592_, v_as_1593_, v_as_x27_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v_as_x27_1594_);
lean_dec(v_as_1593_);
lean_dec_ref(v_lams_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1607_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1614_, lean_object* v_lams_1615_, lean_object* v_as_1616_, size_t v_sz_1617_, size_t v_i_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1618_, v_sz_1617_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_b_1619_);
return v___x_1632_;
}
else
{
lean_object* v_toCold_1633_; lean_object* v_options_1634_; lean_object* v_inheritedTraceOptions_1635_; uint8_t v_hasTrace_1636_; lean_object* v___x_1637_; lean_object* v_a_1638_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; 
v_toCold_1633_ = lean_ctor_get(v___y_1628_, 0);
v_options_1634_ = lean_ctor_get(v_toCold_1633_, 2);
v_inheritedTraceOptions_1635_ = lean_ctor_get(v_toCold_1633_, 11);
v_hasTrace_1636_ = lean_ctor_get_uint8(v_options_1634_, sizeof(void*)*1);
v___x_1637_ = lean_box(0);
v_a_1638_ = lean_array_uget_borrowed(v_as_1616_, v_i_1618_);
if (v_hasTrace_1636_ == 0)
{
v___y_1640_ = v___y_1620_;
v___y_1641_ = v___y_1621_;
v___y_1642_ = v___y_1622_;
v___y_1643_ = v___y_1623_;
v___y_1644_ = v___y_1624_;
v___y_1645_ = v___y_1625_;
v___y_1646_ = v___y_1626_;
v___y_1647_ = v___y_1627_;
v___y_1648_ = v___y_1628_;
v___y_1649_ = v___y_1629_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1665_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1666_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1635_, v_options_1634_, v___x_1666_);
if (v___x_1667_ == 0)
{
v___y_1640_ = v___y_1620_;
v___y_1641_ = v___y_1621_;
v___y_1642_ = v___y_1622_;
v___y_1643_ = v___y_1623_;
v___y_1644_ = v___y_1624_;
v___y_1645_ = v___y_1625_;
v___y_1646_ = v___y_1626_;
v___y_1647_ = v___y_1627_;
v___y_1648_ = v___y_1628_;
v___y_1649_ = v___y_1629_;
goto v___jp_1639_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Grind_updateLastTag(v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref_known(v___x_1668_, 1);
v___x_1669_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1638_, v___y_1620_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1638_);
v___x_1672_ = l_Lean_MessageData_ofExpr(v_a_1638_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1670_);
lean_dec(v_a_1670_);
v___x_1677_ = lean_box(0);
v___x_1678_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1676_, v___x_1677_);
v___x_1679_ = l_Lean_MessageData_ofList(v___x_1678_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1675_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1665_, v___x_1680_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_dec_ref_known(v___x_1681_, 1);
v___y_1640_ = v___y_1620_;
v___y_1641_ = v___y_1621_;
v___y_1642_ = v___y_1622_;
v___y_1643_ = v___y_1623_;
v___y_1644_ = v___y_1624_;
v___y_1645_ = v___y_1625_;
v___y_1646_ = v___y_1626_;
v___y_1647_ = v___y_1627_;
v___y_1648_ = v___y_1628_;
v___y_1649_ = v___y_1629_;
goto v___jp_1639_;
}
else
{
return v___x_1681_;
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1669_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1669_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
return v___x_1668_;
}
}
}
v___jp_1639_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1638_, v___y_1640_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1651_);
lean_dec(v_a_1651_);
v___x_1653_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1614_, v_lams_1615_, v___x_1652_, v___x_1652_, v___x_1637_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___x_1652_);
if (lean_obj_tag(v___x_1653_) == 0)
{
size_t v___x_1654_; size_t v___x_1655_; 
lean_dec_ref_known(v___x_1653_, 1);
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_add(v_i_1618_, v___x_1654_);
v_i_1618_ = v___x_1655_;
v_b_1619_ = v___x_1637_;
goto _start;
}
else
{
return v___x_1653_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1650_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1650_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1614_ = stack[0].m_obj;
lean_object* v_lams_1615_ = stack[1].m_obj;
lean_object* v_as_1616_ = stack[2].m_obj;
size_t v_sz_1617_ = stack[3].m_num;
size_t v_i_1618_ = stack[4].m_num;
lean_object* v_b_1619_ = stack[5].m_obj;
lean_object* v___y_1620_ = stack[6].m_obj;
lean_object* v___y_1621_ = stack[7].m_obj;
lean_object* v___y_1622_ = stack[8].m_obj;
lean_object* v___y_1623_ = stack[9].m_obj;
lean_object* v___y_1624_ = stack[10].m_obj;
lean_object* v___y_1625_ = stack[11].m_obj;
lean_object* v___y_1626_ = stack[12].m_obj;
lean_object* v___y_1627_ = stack[13].m_obj;
lean_object* v___y_1628_ = stack[14].m_obj;
lean_object* v___y_1629_ = stack[15].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1614_, v_lams_1615_, v_as_1616_, v_sz_1617_, v_i_1618_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1691_ = _args[0];
lean_object* v_lams_1692_ = _args[1];
lean_object* v_as_1693_ = _args[2];
lean_object* v_sz_1694_ = _args[3];
lean_object* v_i_1695_ = _args[4];
lean_object* v_b_1696_ = _args[5];
lean_object* v___y_1697_ = _args[6];
lean_object* v___y_1698_ = _args[7];
lean_object* v___y_1699_ = _args[8];
lean_object* v___y_1700_ = _args[9];
lean_object* v___y_1701_ = _args[10];
lean_object* v___y_1702_ = _args[11];
lean_object* v___y_1703_ = _args[12];
lean_object* v___y_1704_ = _args[13];
lean_object* v___y_1705_ = _args[14];
lean_object* v___y_1706_ = _args[15];
lean_object* v___y_1707_ = _args[16];
_start:
{
size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1691_, v_lams_1692_, v_as_1693_, v_sz_boxed_1708_, v_i_boxed_1709_, v_b_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v_as_1693_);
lean_dec_ref(v_lams_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1710_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1711_, lean_object* v_lams_1712_, lean_object* v_as_1713_, size_t v_sz_1714_, size_t v_i_1715_, lean_object* v_b_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_usize_dec_lt(v_i_1715_, v_sz_1714_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_b_1716_);
return v___x_1729_;
}
else
{
lean_object* v_toCold_1730_; lean_object* v_options_1731_; lean_object* v_inheritedTraceOptions_1732_; uint8_t v_hasTrace_1733_; lean_object* v___x_1734_; lean_object* v_a_1735_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; 
v_toCold_1730_ = lean_ctor_get(v___y_1725_, 0);
v_options_1731_ = lean_ctor_get(v_toCold_1730_, 2);
v_inheritedTraceOptions_1732_ = lean_ctor_get(v_toCold_1730_, 11);
v_hasTrace_1733_ = lean_ctor_get_uint8(v_options_1731_, sizeof(void*)*1);
v___x_1734_ = lean_box(0);
v_a_1735_ = lean_array_uget_borrowed(v_as_1713_, v_i_1715_);
if (v_hasTrace_1733_ == 0)
{
v___y_1737_ = v___y_1717_;
v___y_1738_ = v___y_1718_;
v___y_1739_ = v___y_1719_;
v___y_1740_ = v___y_1720_;
v___y_1741_ = v___y_1721_;
v___y_1742_ = v___y_1722_;
v___y_1743_ = v___y_1723_;
v___y_1744_ = v___y_1724_;
v___y_1745_ = v___y_1725_;
v___y_1746_ = v___y_1726_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1763_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1732_, v_options_1731_, v___x_1763_);
if (v___x_1764_ == 0)
{
v___y_1737_ = v___y_1717_;
v___y_1738_ = v___y_1718_;
v___y_1739_ = v___y_1719_;
v___y_1740_ = v___y_1720_;
v___y_1741_ = v___y_1721_;
v___y_1742_ = v___y_1722_;
v___y_1743_ = v___y_1723_;
v___y_1744_ = v___y_1724_;
v___y_1745_ = v___y_1725_;
v___y_1746_ = v___y_1726_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_updateLastTag(v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref_known(v___x_1765_, 1);
v___x_1766_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1735_, v___y_1717_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1735_);
v___x_1769_ = l_Lean_MessageData_ofExpr(v_a_1735_);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1767_);
lean_dec(v_a_1767_);
v___x_1774_ = lean_box(0);
v___x_1775_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1773_, v___x_1774_);
v___x_1776_ = l_Lean_MessageData_ofList(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1772_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1762_, v___x_1777_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref_known(v___x_1778_, 1);
v___y_1737_ = v___y_1717_;
v___y_1738_ = v___y_1718_;
v___y_1739_ = v___y_1719_;
v___y_1740_ = v___y_1720_;
v___y_1741_ = v___y_1721_;
v___y_1742_ = v___y_1722_;
v___y_1743_ = v___y_1723_;
v___y_1744_ = v___y_1724_;
v___y_1745_ = v___y_1725_;
v___y_1746_ = v___y_1726_;
goto v___jp_1736_;
}
else
{
return v___x_1778_;
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1766_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1766_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
return v___x_1765_;
}
}
}
v___jp_1736_:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1735_, v___y_1737_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1748_);
lean_dec(v_a_1748_);
v___x_1750_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1711_, v_lams_1712_, v___x_1749_, v___x_1749_, v___x_1734_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___x_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref_known(v___x_1750_, 1);
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1715_, v___x_1751_);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1711_, v_lams_1712_, v_as_1713_, v_sz_1714_, v___x_1752_, v___x_1734_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1753_;
}
else
{
return v___x_1750_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1747_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1747_);
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
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1711_ = stack[0].m_obj;
lean_object* v_lams_1712_ = stack[1].m_obj;
lean_object* v_as_1713_ = stack[2].m_obj;
size_t v_sz_1714_ = stack[3].m_num;
size_t v_i_1715_ = stack[4].m_num;
lean_object* v_b_1716_ = stack[5].m_obj;
lean_object* v___y_1717_ = stack[6].m_obj;
lean_object* v___y_1718_ = stack[7].m_obj;
lean_object* v___y_1719_ = stack[8].m_obj;
lean_object* v___y_1720_ = stack[9].m_obj;
lean_object* v___y_1721_ = stack[10].m_obj;
lean_object* v___y_1722_ = stack[11].m_obj;
lean_object* v___y_1723_ = stack[12].m_obj;
lean_object* v___y_1724_ = stack[13].m_obj;
lean_object* v___y_1725_ = stack[14].m_obj;
lean_object* v___y_1726_ = stack[15].m_obj;
lean_object* v_res_1787_;
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1711_, v_lams_1712_, v_as_1713_, v_sz_1714_, v_i_1715_, v_b_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1788_ = _args[0];
lean_object* v_lams_1789_ = _args[1];
lean_object* v_as_1790_ = _args[2];
lean_object* v_sz_1791_ = _args[3];
lean_object* v_i_1792_ = _args[4];
lean_object* v_b_1793_ = _args[5];
lean_object* v___y_1794_ = _args[6];
lean_object* v___y_1795_ = _args[7];
lean_object* v___y_1796_ = _args[8];
lean_object* v___y_1797_ = _args[9];
lean_object* v___y_1798_ = _args[10];
lean_object* v___y_1799_ = _args[11];
lean_object* v___y_1800_ = _args[12];
lean_object* v___y_1801_ = _args[13];
lean_object* v___y_1802_ = _args[14];
lean_object* v___y_1803_ = _args[15];
lean_object* v___y_1804_ = _args[16];
_start:
{
size_t v_sz_boxed_1805_; size_t v_i_boxed_1806_; lean_object* v_res_1807_; 
v_sz_boxed_1805_ = lean_unbox_usize(v_sz_1791_);
lean_dec(v_sz_1791_);
v_i_boxed_1806_ = lean_unbox_usize(v_i_1792_);
lean_dec(v_i_1792_);
v_res_1807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1788_, v_lams_1789_, v_as_1790_, v_sz_boxed_1805_, v_i_boxed_1806_, v_b_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v_as_1790_);
lean_dec_ref(v_lams_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1814_, lean_object* v_fns_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_array_get_size(v_lams_1814_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_nat_dec_eq(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = l_Lean_instInhabitedExpr;
v___x_1831_ = lean_unsigned_to_nat(1u);
v___x_1832_ = lean_nat_sub(v___x_1827_, v___x_1831_);
v___x_1833_ = lean_array_get_borrowed(v___x_1830_, v_lams_1814_, v___x_1832_);
lean_dec(v___x_1832_);
v___x_1834_ = lean_st_ref_get(v_a_1816_);
lean_inc(v___x_1833_);
v___x_1835_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1834_, v___x_1833_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
lean_dec(v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v_toCold_1860_; lean_object* v_options_1861_; uint8_t v_hasTrace_1862_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v_toCold_1860_ = lean_ctor_get(v_a_1824_, 0);
v_options_1861_ = lean_ctor_get(v_toCold_1860_, 2);
v_hasTrace_1862_ = lean_ctor_get_uint8(v_options_1861_, sizeof(void*)*1);
if (v_hasTrace_1862_ == 0)
{
v___y_1838_ = v_a_1816_;
v___y_1839_ = v_a_1817_;
v___y_1840_ = v_a_1818_;
v___y_1841_ = v_a_1819_;
v___y_1842_ = v_a_1820_;
v___y_1843_ = v_a_1821_;
v___y_1844_ = v_a_1822_;
v___y_1845_ = v_a_1823_;
v___y_1846_ = v_a_1824_;
v___y_1847_ = v_a_1825_;
goto v___jp_1837_;
}
else
{
lean_object* v_inheritedTraceOptions_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_inheritedTraceOptions_1863_ = lean_ctor_get(v_toCold_1860_, 11);
v___x_1864_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1865_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1863_, v_options_1861_, v___x_1865_);
if (v___x_1866_ == 0)
{
v___y_1838_ = v_a_1816_;
v___y_1839_ = v_a_1817_;
v___y_1840_ = v_a_1818_;
v___y_1841_ = v_a_1819_;
v___y_1842_ = v_a_1820_;
v___y_1843_ = v_a_1821_;
v___y_1844_ = v_a_1822_;
v___y_1845_ = v_a_1823_;
v___y_1846_ = v_a_1824_;
v___y_1847_ = v_a_1825_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_Grind_updateLastTag(v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1867_, 1);
v___x_1868_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1815_);
v___x_1869_ = lean_array_to_list(v_fns_1815_);
v___x_1870_ = lean_box(0);
v___x_1871_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1869_, v___x_1870_);
v___x_1872_ = l_Lean_MessageData_ofList(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1868_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_inc_ref(v_lams_1814_);
v___x_1876_ = lean_array_to_list(v_lams_1814_);
v___x_1877_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1876_, v___x_1870_);
v___x_1878_ = l_Lean_MessageData_ofList(v___x_1877_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1875_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1864_, v___x_1879_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_dec_ref_known(v___x_1880_, 1);
v___y_1838_ = v_a_1816_;
v___y_1839_ = v_a_1817_;
v___y_1840_ = v_a_1818_;
v___y_1841_ = v_a_1819_;
v___y_1842_ = v_a_1820_;
v___y_1843_ = v_a_1821_;
v___y_1844_ = v_a_1822_;
v___y_1845_ = v_a_1823_;
v___y_1846_ = v_a_1824_;
v___y_1847_ = v_a_1825_;
goto v___jp_1837_;
}
else
{
lean_dec(v_a_1836_);
lean_dec_ref(v_fns_1815_);
lean_dec_ref(v_lams_1814_);
return v___x_1880_;
}
}
else
{
lean_dec(v_a_1836_);
lean_dec_ref(v_fns_1815_);
lean_dec_ref(v_lams_1814_);
return v___x_1867_;
}
}
}
v___jp_1837_:
{
lean_object* v___x_1848_; size_t v_sz_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1848_ = lean_box(0);
v_sz_1849_ = lean_array_size(v_fns_1815_);
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1836_, v_lams_1814_, v_fns_1815_, v_sz_1849_, v___x_1850_, v___x_1848_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec_ref(v_fns_1815_);
lean_dec_ref(v_lams_1814_);
lean_dec(v_a_1836_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1859_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1848_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1848_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_fns_1815_);
lean_dec_ref(v_lams_1814_);
v_a_1881_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1835_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1835_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref(v_fns_1815_);
lean_dec_ref(v_lams_1814_);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBeta_0interp(lean_interpreter_value* stack)
{
lean_object* v_lams_1814_ = stack[0].m_obj;
lean_object* v_fns_1815_ = stack[1].m_obj;
lean_object* v_a_1816_ = stack[2].m_obj;
lean_object* v_a_1817_ = stack[3].m_obj;
lean_object* v_a_1818_ = stack[4].m_obj;
lean_object* v_a_1819_ = stack[5].m_obj;
lean_object* v_a_1820_ = stack[6].m_obj;
lean_object* v_a_1821_ = stack[7].m_obj;
lean_object* v_a_1822_ = stack[8].m_obj;
lean_object* v_a_1823_ = stack[9].m_obj;
lean_object* v_a_1824_ = stack[10].m_obj;
lean_object* v_a_1825_ = stack[11].m_obj;
lean_object* v_res_1891_;
v_res_1891_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1814_, v_fns_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
stack->m_obj
 = v_res_1891_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1892_, lean_object* v_fns_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1892_, v_fns_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1905_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_lams_1908_, lean_object* v_inst_1909_, lean_object* v_a_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1906_, v_a_1907_, v_lams_1908_, v_a_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1906_ = stack[0].m_obj;
lean_object* v_a_1907_ = stack[1].m_obj;
lean_object* v_lams_1908_ = stack[2].m_obj;
lean_object* v_a_1910_ = stack[4].m_obj;
lean_object* v___y_1911_ = stack[5].m_obj;
lean_object* v___y_1912_ = stack[6].m_obj;
lean_object* v___y_1913_ = stack[7].m_obj;
lean_object* v___y_1914_ = stack[8].m_obj;
lean_object* v___y_1915_ = stack[9].m_obj;
lean_object* v___y_1916_ = stack[10].m_obj;
lean_object* v___y_1917_ = stack[11].m_obj;
lean_object* v___y_1918_ = stack[12].m_obj;
lean_object* v___y_1919_ = stack[13].m_obj;
lean_object* v___y_1920_ = stack[14].m_obj;
lean_object* v_res_1923_;
v_res_1923_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1906_, v_a_1907_, v_lams_1908_, lean_box(0), v_a_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
stack->m_obj
 = v_res_1923_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_lams_1926_, lean_object* v_inst_1927_, lean_object* v_a_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1924_, v_a_1925_, v_lams_1926_, v_inst_1927_, v_a_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
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
lean_dec_ref(v_lams_1926_);
lean_dec_ref(v_a_1925_);
lean_dec_ref(v_a_1924_);
return v_res_1940_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1941_, lean_object* v_lams_1942_, lean_object* v_as_1943_, lean_object* v_as_x27_1944_, lean_object* v_b_1945_, lean_object* v_a_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1941_, v_lams_1942_, v_as_1943_, v_as_x27_1944_, v_b_1945_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1941_ = stack[0].m_obj;
lean_object* v_lams_1942_ = stack[1].m_obj;
lean_object* v_as_1943_ = stack[2].m_obj;
lean_object* v_as_x27_1944_ = stack[3].m_obj;
lean_object* v_b_1945_ = stack[4].m_obj;
lean_object* v___y_1947_ = stack[6].m_obj;
lean_object* v___y_1948_ = stack[7].m_obj;
lean_object* v___y_1949_ = stack[8].m_obj;
lean_object* v___y_1950_ = stack[9].m_obj;
lean_object* v___y_1951_ = stack[10].m_obj;
lean_object* v___y_1952_ = stack[11].m_obj;
lean_object* v___y_1953_ = stack[12].m_obj;
lean_object* v___y_1954_ = stack[13].m_obj;
lean_object* v___y_1955_ = stack[14].m_obj;
lean_object* v___y_1956_ = stack[15].m_obj;
lean_object* v_res_1959_;
v_res_1959_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1941_, v_lams_1942_, v_as_1943_, v_as_x27_1944_, v_b_1945_, lean_box(0), v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1960_ = _args[0];
lean_object* v_lams_1961_ = _args[1];
lean_object* v_as_1962_ = _args[2];
lean_object* v_as_x27_1963_ = _args[3];
lean_object* v_b_1964_ = _args[4];
lean_object* v_a_1965_ = _args[5];
lean_object* v___y_1966_ = _args[6];
lean_object* v___y_1967_ = _args[7];
lean_object* v___y_1968_ = _args[8];
lean_object* v___y_1969_ = _args[9];
lean_object* v___y_1970_ = _args[10];
lean_object* v___y_1971_ = _args[11];
lean_object* v___y_1972_ = _args[12];
lean_object* v___y_1973_ = _args[13];
lean_object* v___y_1974_ = _args[14];
lean_object* v___y_1975_ = _args[15];
lean_object* v___y_1976_ = _args[16];
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1960_, v_lams_1961_, v_as_1962_, v_as_x27_1963_, v_b_1964_, v_a_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec(v_as_x27_1963_);
lean_dec(v_as_1962_);
lean_dec_ref(v_lams_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1977_;
}
}
lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1978_, lean_object* v_lams_1979_, lean_object* v_as_1980_, lean_object* v_as_x27_1981_, lean_object* v_b_1982_, lean_object* v_a_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1978_, v_lams_1979_, v_as_x27_1981_, v_b_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1978_ = stack[0].m_obj;
lean_object* v_lams_1979_ = stack[1].m_obj;
lean_object* v_as_1980_ = stack[2].m_obj;
lean_object* v_as_x27_1981_ = stack[3].m_obj;
lean_object* v_b_1982_ = stack[4].m_obj;
lean_object* v___y_1984_ = stack[6].m_obj;
lean_object* v___y_1985_ = stack[7].m_obj;
lean_object* v___y_1986_ = stack[8].m_obj;
lean_object* v___y_1987_ = stack[9].m_obj;
lean_object* v___y_1988_ = stack[10].m_obj;
lean_object* v___y_1989_ = stack[11].m_obj;
lean_object* v___y_1990_ = stack[12].m_obj;
lean_object* v___y_1991_ = stack[13].m_obj;
lean_object* v___y_1992_ = stack[14].m_obj;
lean_object* v___y_1993_ = stack[15].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1978_, v_lams_1979_, v_as_1980_, v_as_x27_1981_, v_b_1982_, lean_box(0), v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
stack->m_obj
 = v_res_1996_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1997_ = _args[0];
lean_object* v_lams_1998_ = _args[1];
lean_object* v_as_1999_ = _args[2];
lean_object* v_as_x27_2000_ = _args[3];
lean_object* v_b_2001_ = _args[4];
lean_object* v_a_2002_ = _args[5];
lean_object* v___y_2003_ = _args[6];
lean_object* v___y_2004_ = _args[7];
lean_object* v___y_2005_ = _args[8];
lean_object* v___y_2006_ = _args[9];
lean_object* v___y_2007_ = _args[10];
lean_object* v___y_2008_ = _args[11];
lean_object* v___y_2009_ = _args[12];
lean_object* v___y_2010_ = _args[13];
lean_object* v___y_2011_ = _args[14];
lean_object* v___y_2012_ = _args[15];
lean_object* v___y_2013_ = _args[16];
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1997_, v_lams_1998_, v_as_1999_, v_as_x27_2000_, v_b_2001_, v_a_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v_as_x27_2000_);
lean_dec(v_as_1999_);
lean_dec_ref(v_lams_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2014_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_2018_, lean_object* v_as_2019_, size_t v_sz_2020_, size_t v_i_2021_, lean_object* v_b_2022_){
_start:
{
lean_object* v_a_2024_; uint8_t v___x_2028_; 
v___x_2028_ = lean_usize_dec_lt(v_i_2021_, v_sz_2020_);
if (v___x_2028_ == 0)
{
lean_inc_ref(v_b_2022_);
return v_b_2022_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v_a_2031_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_2031_ = lean_array_uget_borrowed(v_as_2019_, v_i_2021_);
if (lean_obj_tag(v_a_2031_) == 6)
{
lean_object* v_binderType_2032_; size_t v___x_2033_; size_t v___x_2034_; uint8_t v___x_2035_; 
v_binderType_2032_ = lean_ctor_get(v_a_2031_, 1);
v___x_2033_ = lean_ptr_addr(v_d_2018_);
v___x_2034_ = lean_ptr_addr(v_binderType_2032_);
v___x_2035_ = lean_usize_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
v_a_2024_ = v___x_2030_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_inc_ref(v_a_2031_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_a_2031_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
lean_ctor_set(v___x_2038_, 1, v___x_2029_);
return v___x_2038_;
}
}
else
{
v_a_2024_ = v___x_2030_;
goto v___jp_2023_;
}
}
v___jp_2023_:
{
size_t v___x_2025_; size_t v___x_2026_; 
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2021_, v___x_2025_);
v_i_2021_ = v___x_2026_;
v_b_2022_ = v_a_2024_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2018_ = stack[0].m_obj;
lean_object* v_as_2019_ = stack[1].m_obj;
size_t v_sz_2020_ = stack[2].m_num;
size_t v_i_2021_ = stack[3].m_num;
lean_object* v_b_2022_ = stack[4].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2018_, v_as_2019_, v_sz_2020_, v_i_2021_, v_b_2022_);
stack->m_obj
 = v_res_2039_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2040_, lean_object* v_as_2041_, lean_object* v_sz_2042_, lean_object* v_i_2043_, lean_object* v_b_2044_){
_start:
{
size_t v_sz_boxed_2045_; size_t v_i_boxed_2046_; lean_object* v_res_2047_; 
v_sz_boxed_2045_ = lean_unbox_usize(v_sz_2042_);
lean_dec(v_sz_2042_);
v_i_boxed_2046_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_res_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2040_, v_as_2041_, v_sz_boxed_2045_, v_i_boxed_2046_, v_b_2044_);
lean_dec_ref(v_b_2044_);
lean_dec_ref(v_as_2041_);
lean_dec_ref(v_d_2040_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2048_, lean_object* v_d_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v_sz_2052_; size_t v___x_2053_; lean_object* v___x_2054_; lean_object* v_fst_2055_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2052_ = lean_array_size(v_lams_2048_);
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2049_, v_lams_2048_, v_sz_2052_, v___x_2053_, v___x_2051_);
v_fst_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_fst_2055_);
lean_dec_ref(v___x_2054_);
if (lean_obj_tag(v_fst_2055_) == 0)
{
return v___x_2050_;
}
else
{
lean_object* v_val_2056_; 
v_val_2056_ = lean_ctor_get(v_fst_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v_fst_2055_, 1);
return v_val_2056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2057_, lean_object* v_d_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2057_, v_d_2058_);
lean_dec_ref(v_d_2058_);
lean_dec_ref(v_lams_2057_);
return v_res_2059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2070_, lean_object* v_lams_u2081_2071_, lean_object* v_as_2072_, size_t v_sz_2073_, size_t v_i_2074_, lean_object* v_b_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_a_2088_; uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2074_, v_sz_2073_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2075_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v_a_2095_; 
v___x_2094_ = lean_box(0);
v_a_2095_ = lean_array_uget_borrowed(v_as_2072_, v_i_2074_);
if (lean_obj_tag(v_a_2095_) == 6)
{
lean_object* v_binderType_2096_; lean_object* v_body_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_binderType_2096_ = lean_ctor_get(v_a_2095_, 1);
v_body_2097_ = lean_ctor_get(v_a_2095_, 2);
v___x_2098_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2096_);
v___x_2099_ = l_Lean_Meta_getLevel(v_binderType_2096_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_a_2100_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
lean_inc_ref(v___x_2103_);
v___x_2104_ = l_Lean_mkConst(v___x_2101_, v___x_2103_);
lean_inc_ref(v_binderType_2096_);
v___x_2105_ = l_Lean_Expr_app___override(v___x_2104_, v_binderType_2096_);
v___x_2106_ = lean_box(0);
v___x_2107_ = l_Lean_Meta_synthInstance_x3f(v___x_2105_, v___x_2106_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
if (lean_obj_tag(v_a_2108_) == 1)
{
lean_object* v_val_2109_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; uint8_t v___x_2174_; 
v_val_2109_ = lean_ctor_get(v_a_2108_, 0);
lean_inc(v_val_2109_);
lean_dec_ref_known(v_a_2108_, 1);
v___x_2174_ = l_Lean_Expr_hasLooseBVars(v_body_2097_);
if (v___x_2174_ == 0)
{
v___y_2111_ = v___y_2076_;
v___y_2112_ = v___y_2077_;
v___y_2113_ = v___y_2078_;
v___y_2114_ = v___y_2079_;
v___y_2115_ = v___y_2080_;
v___y_2116_ = v___y_2081_;
v___y_2117_ = v___y_2082_;
v___y_2118_ = v___y_2083_;
v___y_2119_ = v___y_2084_;
v___y_2120_ = v___y_2085_;
goto v___jp_2110_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2103_);
v___x_2176_ = l_Lean_mkConst(v___x_2175_, v___x_2103_);
lean_inc_ref(v_binderType_2096_);
v___x_2177_ = l_Lean_Expr_app___override(v___x_2176_, v_binderType_2096_);
v___x_2178_ = l_Lean_Meta_synthInstance_x3f(v___x_2177_, v___x_2106_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_dec(v_val_2109_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
else
{
lean_dec_ref_known(v_a_2179_, 1);
if (v___x_2174_ == 0)
{
lean_dec(v_val_2109_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
else
{
v___y_2111_ = v___y_2076_;
v___y_2112_ = v___y_2077_;
v___y_2113_ = v___y_2078_;
v___y_2114_ = v___y_2079_;
v___y_2115_ = v___y_2080_;
v___y_2116_ = v___y_2081_;
v___y_2117_ = v___y_2082_;
v___y_2118_ = v___y_2083_;
v___y_2119_ = v___y_2084_;
v___y_2120_ = v___y_2085_;
goto v___jp_2110_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_val_2109_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2180_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2178_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2178_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
v___jp_2110_:
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2070_, v_binderType_2096_);
if (lean_obj_tag(v___x_2121_) == 1)
{
lean_object* v_val_2122_; 
v_val_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_val_2122_);
lean_dec_ref_known(v___x_2121_, 1);
if (lean_obj_tag(v_val_2122_) == 6)
{
lean_object* v_binderType_2123_; lean_object* v_body_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_binderType_2123_ = lean_ctor_get(v_val_2122_, 1);
lean_inc_ref(v_binderType_2123_);
v_body_2124_ = lean_ctor_get(v_val_2122_, 2);
lean_inc_ref(v_body_2124_);
lean_dec_ref_known(v_val_2122_, 3);
v___x_2125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2126_ = l_Lean_mkConst(v___x_2125_, v___x_2103_);
v___x_2127_ = l_Lean_mkAppB(v___x_2126_, v_binderType_2123_, v_val_2109_);
v___x_2128_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2127_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = lean_expr_instantiate1(v_body_2097_, v_a_2129_);
v___x_2131_ = lean_expr_instantiate1(v_body_2124_, v_a_2129_);
lean_dec_ref(v_body_2124_);
v___x_2132_ = lean_array_fget_borrowed(v_lams_u2081_2071_, v___x_2098_);
v___x_2133_ = lean_array_fget_borrowed(v_lams_u2082_2070_, v___x_2098_);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc(v___x_2133_);
lean_inc(v___x_2132_);
v___x_2134_ = lean_grind_mk_eq_proof(v___x_2132_, v___x_2133_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_Meta_mkCongrFun(v_a_2135_, v_a_2129_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Meta_mkEq(v___x_2130_, v___x_2131_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = l_Lean_Meta_mkExpectedPropHint(v_a_2137_, v_a_2139_);
v___x_2141_ = l_Lean_Meta_Grind_pushNewFact(v___x_2140_, v___x_2098_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref_known(v___x_2141_, 1);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
else
{
return v___x_2141_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_a_2137_);
v_a_2142_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2138_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2138_);
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
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
v_a_2150_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2136_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2136_);
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
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v___x_2131_);
lean_dec_ref(v___x_2130_);
lean_dec(v_a_2129_);
v_a_2158_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2134_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2134_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_body_2124_);
v_a_2166_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2128_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2128_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_dec(v_val_2122_);
lean_dec(v_val_2109_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
}
else
{
lean_dec(v___x_2121_);
lean_dec(v_val_2109_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
}
}
else
{
lean_dec(v_a_2108_);
lean_dec_ref_known(v___x_2103_, 2);
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref_known(v___x_2103_, 2);
v_a_2188_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2107_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2107_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_a_2196_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2099_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2099_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
v_a_2088_ = v___x_2094_;
goto v___jp_2087_;
}
}
v___jp_2087_:
{
size_t v___x_2089_; size_t v___x_2090_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2074_, v___x_2089_);
v_i_2074_ = v___x_2090_;
v_b_2075_ = v_a_2088_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lams_u2082_2070_ = stack[0].m_obj;
lean_object* v_lams_u2081_2071_ = stack[1].m_obj;
lean_object* v_as_2072_ = stack[2].m_obj;
size_t v_sz_2073_ = stack[3].m_num;
size_t v_i_2074_ = stack[4].m_num;
lean_object* v_b_2075_ = stack[5].m_obj;
lean_object* v___y_2076_ = stack[6].m_obj;
lean_object* v___y_2077_ = stack[7].m_obj;
lean_object* v___y_2078_ = stack[8].m_obj;
lean_object* v___y_2079_ = stack[9].m_obj;
lean_object* v___y_2080_ = stack[10].m_obj;
lean_object* v___y_2081_ = stack[11].m_obj;
lean_object* v___y_2082_ = stack[12].m_obj;
lean_object* v___y_2083_ = stack[13].m_obj;
lean_object* v___y_2084_ = stack[14].m_obj;
lean_object* v___y_2085_ = stack[15].m_obj;
lean_object* v_res_2204_;
v_res_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2070_, v_lams_u2081_2071_, v_as_2072_, v_sz_2073_, v_i_2074_, v_b_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2204_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2205_ = _args[0];
lean_object* v_lams_u2081_2206_ = _args[1];
lean_object* v_as_2207_ = _args[2];
lean_object* v_sz_2208_ = _args[3];
lean_object* v_i_2209_ = _args[4];
lean_object* v_b_2210_ = _args[5];
lean_object* v___y_2211_ = _args[6];
lean_object* v___y_2212_ = _args[7];
lean_object* v___y_2213_ = _args[8];
lean_object* v___y_2214_ = _args[9];
lean_object* v___y_2215_ = _args[10];
lean_object* v___y_2216_ = _args[11];
lean_object* v___y_2217_ = _args[12];
lean_object* v___y_2218_ = _args[13];
lean_object* v___y_2219_ = _args[14];
lean_object* v___y_2220_ = _args[15];
lean_object* v___y_2221_ = _args[16];
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2208_);
lean_dec(v_sz_2208_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2205_, v_lams_u2081_2206_, v_as_2207_, v_sz_boxed_2222_, v_i_boxed_2223_, v_b_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v_as_2207_);
lean_dec_ref(v_lams_u2081_2206_);
lean_dec_ref(v_lams_u2082_2205_);
return v_res_2224_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2225_, lean_object* v_lams_u2082_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = lean_array_get_size(v_lams_u2081_2225_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_nat_dec_eq(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_array_get_size(v_lams_u2082_2226_);
v___x_2242_ = lean_nat_dec_eq(v___x_2241_, v___x_2239_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; size_t v_sz_2244_; size_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2243_ = lean_box(0);
v_sz_2244_ = lean_array_size(v_lams_u2081_2225_);
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2226_, v_lams_u2081_2225_, v_lams_u2081_2225_, v_sz_2244_, v___x_2245_, v___x_2243_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2246_, 0);
lean_dec(v_unused_2254_);
v___x_2248_ = v___x_2246_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v___x_2246_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2243_);
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2243_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
return v___x_2246_;
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_0interp(lean_interpreter_value* stack)
{
lean_object* v_lams_u2081_2225_ = stack[0].m_obj;
lean_object* v_lams_u2082_2226_ = stack[1].m_obj;
lean_object* v_a_2227_ = stack[2].m_obj;
lean_object* v_a_2228_ = stack[3].m_obj;
lean_object* v_a_2229_ = stack[4].m_obj;
lean_object* v_a_2230_ = stack[5].m_obj;
lean_object* v_a_2231_ = stack[6].m_obj;
lean_object* v_a_2232_ = stack[7].m_obj;
lean_object* v_a_2233_ = stack[8].m_obj;
lean_object* v_a_2234_ = stack[9].m_obj;
lean_object* v_a_2235_ = stack[10].m_obj;
lean_object* v_a_2236_ = stack[11].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2225_, v_lams_u2082_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2260_, lean_object* v_lams_u2082_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2260_, v_lams_u2082_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_lams_u2082_2261_);
lean_dec_ref(v_lams_u2081_2260_);
return v_res_2273_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2274_){
_start:
{
uint8_t v___x_2275_; 
v___x_2275_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2274_ = stack[0].m_obj;
uint8_t v_res_2276_;
v_res_2276_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2274_);
stack->m_num = v_res_2276_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2277_){
_start:
{
uint8_t v_res_2278_; lean_object* v_r_2279_; 
v_res_2278_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2277_);
lean_dec_ref(v_x_2277_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2280_, lean_object* v_x_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2281_ = stack[1].m_obj;
uint8_t v_res_2283_;
v_res_2283_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_box(0), v_x_2281_);
stack->m_num = v_res_2283_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_x_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2284_, v_x_2285_);
lean_dec_ref(v_x_2285_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2288_, lean_object* v_v_2289_, lean_object* v_i_2290_){
_start:
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_array_get_size(v_xs_2288_);
v___x_2292_ = lean_nat_dec_lt(v_i_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_dec(v_i_2290_);
v___x_2293_ = lean_box(0);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; size_t v___x_2295_; size_t v___x_2296_; uint8_t v___x_2297_; 
v___x_2294_ = lean_array_fget_borrowed(v_xs_2288_, v_i_2290_);
v___x_2295_ = lean_ptr_addr(v___x_2294_);
v___x_2296_ = lean_ptr_addr(v_v_2289_);
v___x_2297_ = lean_usize_dec_eq(v___x_2295_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_add(v_i_2290_, v___x_2298_);
lean_dec(v_i_2290_);
v_i_2290_ = v___x_2299_;
goto _start;
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_i_2290_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2302_, lean_object* v_v_2303_, lean_object* v_i_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2302_, v_v_2303_, v_i_2304_);
lean_dec_ref(v_v_2303_);
lean_dec_ref(v_xs_2302_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2306_, lean_object* v_v_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2306_, v_v_2307_, v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2310_, lean_object* v_v_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2310_, v_v_2311_);
lean_dec_ref(v_v_2311_);
lean_dec_ref(v_xs_2310_);
return v_res_2312_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2313_, size_t v_x_2314_, lean_object* v_x_2315_){
_start:
{
if (lean_obj_tag(v_x_2313_) == 0)
{
lean_object* v_es_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v_j_2320_; lean_object* v_entry_2321_; 
v_es_2316_ = lean_ctor_get(v_x_2313_, 0);
v___x_2317_ = lean_box(2);
v___x_2318_ = ((size_t)31ULL);
v___x_2319_ = lean_usize_land(v_x_2314_, v___x_2318_);
v_j_2320_ = lean_usize_to_nat(v___x_2319_);
v_entry_2321_ = lean_array_get(v___x_2317_, v_es_2316_, v_j_2320_);
switch(lean_obj_tag(v_entry_2321_))
{
case 0:
{
lean_object* v_key_2322_; size_t v___x_2323_; size_t v___x_2324_; uint8_t v___x_2325_; 
v_key_2322_ = lean_ctor_get(v_entry_2321_, 0);
lean_inc(v_key_2322_);
lean_dec_ref_known(v_entry_2321_, 2);
v___x_2323_ = lean_ptr_addr(v_x_2315_);
v___x_2324_ = lean_ptr_addr(v_key_2322_);
lean_dec(v_key_2322_);
v___x_2325_ = lean_usize_dec_eq(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec(v_j_2320_);
return v_x_2313_;
}
else
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2333_; 
lean_inc_ref(v_es_2316_);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_x_2313_, 0);
lean_dec(v_unused_2334_);
v___x_2327_ = v_x_2313_;
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v_x_2313_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2333_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_array_set(v_es_2316_, v_j_2320_, v___x_2317_);
lean_dec(v_j_2320_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2331_ = v___x_2327_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
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
case 1:
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2369_; 
lean_inc_ref(v_es_2316_);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v_x_2313_, 0);
lean_dec(v_unused_2370_);
v___x_2336_ = v_x_2313_;
v_isShared_2337_ = v_isSharedCheck_2369_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v_x_2313_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2369_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v_node_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2368_; 
v_node_2338_ = lean_ctor_get(v_entry_2321_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_entry_2321_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2340_ = v_entry_2321_;
v_isShared_2341_ = v_isSharedCheck_2368_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_node_2338_);
lean_dec(v_entry_2321_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2368_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
size_t v___x_2342_; lean_object* v_entries_2343_; size_t v___x_2344_; lean_object* v_newNode_2345_; lean_object* v___x_2346_; 
v___x_2342_ = ((size_t)5ULL);
v_entries_2343_ = lean_array_set(v_es_2316_, v_j_2320_, v___x_2317_);
v___x_2344_ = lean_usize_shift_right(v_x_2314_, v___x_2342_);
v_newNode_2345_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2338_, v___x_2344_, v_x_2315_);
lean_inc_ref(v_newNode_2345_);
v___x_2346_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2345_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v___x_2348_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v_newNode_2345_);
v___x_2348_ = v___x_2340_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_newNode_2345_);
v___x_2348_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_array_set(v_entries_2343_, v_j_2320_, v___x_2348_);
lean_dec(v_j_2320_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2349_);
v___x_2351_ = v___x_2336_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_val_2354_; lean_object* v_fst_2355_; lean_object* v_snd_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_newNode_2345_);
lean_del_object(v___x_2340_);
v_val_2354_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v___x_2346_, 1);
v_fst_2355_ = lean_ctor_get(v_val_2354_, 0);
v_snd_2356_ = lean_ctor_get(v_val_2354_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_val_2354_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2358_ = v_val_2354_;
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_snd_2356_);
lean_inc(v_fst_2355_);
lean_dec(v_val_2354_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_fst_2355_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_snd_2356_);
v___x_2361_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_array_set(v_entries_2343_, v_j_2320_, v___x_2361_);
lean_dec(v_j_2320_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2362_);
v___x_2364_ = v___x_2336_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2320_);
return v_x_2313_;
}
}
}
else
{
lean_object* v_ks_2371_; lean_object* v_vs_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2386_; 
v_ks_2371_ = lean_ctor_get(v_x_2313_, 0);
v_vs_2372_ = lean_ctor_get(v_x_2313_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2374_ = v_x_2313_;
v_isShared_2375_ = v_isSharedCheck_2386_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_vs_2372_);
lean_inc(v_ks_2371_);
lean_dec(v_x_2313_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2386_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2371_, v_x_2315_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2378_; 
if (v_isShared_2375_ == 0)
{
v___x_2378_ = v___x_2374_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_ks_2371_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_vs_2372_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
else
{
lean_object* v_val_2380_; lean_object* v_keys_x27_2381_; lean_object* v_vals_x27_2382_; lean_object* v___x_2384_; 
v_val_2380_ = lean_ctor_get(v___x_2376_, 0);
lean_inc_n(v_val_2380_, 2);
lean_dec_ref_known(v___x_2376_, 1);
v_keys_x27_2381_ = l_Array_eraseIdx___redArg(v_ks_2371_, v_val_2380_);
v_vals_x27_2382_ = l_Array_eraseIdx___redArg(v_vs_2372_, v_val_2380_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 1, v_vals_x27_2382_);
lean_ctor_set(v___x_2374_, 0, v_keys_x27_2381_);
v___x_2384_ = v___x_2374_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_keys_x27_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_vals_x27_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2313_ = stack[0].m_obj;
size_t v_x_2314_ = stack[1].m_num;
lean_object* v_x_2315_ = stack[2].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2313_, v_x_2314_, v_x_2315_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
size_t v_x_19408__boxed_2391_; lean_object* v_res_2392_; 
v_x_19408__boxed_2391_ = lean_unbox_usize(v_x_2389_);
lean_dec(v_x_2389_);
v_res_2392_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2388_, v_x_19408__boxed_2391_, v_x_2390_);
lean_dec_ref(v_x_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
size_t v___x_2395_; size_t v___x_2396_; size_t v___x_2397_; uint64_t v___x_2398_; size_t v_h_2399_; lean_object* v___x_2400_; 
v___x_2395_ = lean_ptr_addr(v_x_2394_);
v___x_2396_ = ((size_t)3ULL);
v___x_2397_ = lean_usize_shift_right(v___x_2395_, v___x_2396_);
v___x_2398_ = lean_usize_to_uint64(v___x_2397_);
v_h_2399_ = lean_uint64_to_usize(v___x_2398_);
v___x_2400_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2393_, v_h_2399_, v_x_2394_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2401_, v_x_2402_);
lean_dec_ref(v_x_2402_);
return v_res_2403_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
if (lean_obj_tag(v_as_2404_) == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_box(0);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
else
{
lean_object* v_head_2418_; lean_object* v_tail_2419_; lean_object* v___x_2420_; 
v_head_2418_ = lean_ctor_get(v_as_2404_, 0);
lean_inc(v_head_2418_);
v_tail_2419_ = lean_ctor_get(v_as_2404_, 1);
lean_inc(v_tail_2419_);
lean_dec_ref_known(v_as_2404_, 2);
v___x_2420_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2418_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_dec_ref_known(v___x_2420_, 1);
v_as_2404_ = v_tail_2419_;
goto _start;
}
else
{
lean_dec(v_tail_2419_);
return v___x_2420_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2404_ = stack[0].m_obj;
lean_object* v___y_2405_ = stack[1].m_obj;
lean_object* v___y_2406_ = stack[2].m_obj;
lean_object* v___y_2407_ = stack[3].m_obj;
lean_object* v___y_2408_ = stack[4].m_obj;
lean_object* v___y_2409_ = stack[5].m_obj;
lean_object* v___y_2410_ = stack[6].m_obj;
lean_object* v___y_2411_ = stack[7].m_obj;
lean_object* v___y_2412_ = stack[8].m_obj;
lean_object* v___y_2413_ = stack[9].m_obj;
lean_object* v___y_2414_ = stack[10].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2436_, lean_object* v_vals_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_){
_start:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_array_get_size(v_keys_2436_);
v___x_2441_ = lean_nat_dec_lt(v_i_2438_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
lean_dec(v_i_2438_);
v___x_2442_ = lean_box(0);
return v___x_2442_;
}
else
{
lean_object* v_k_x27_2443_; size_t v___x_2444_; size_t v___x_2445_; uint8_t v___x_2446_; 
v_k_x27_2443_ = lean_array_fget_borrowed(v_keys_2436_, v_i_2438_);
v___x_2444_ = lean_ptr_addr(v_k_2439_);
v___x_2445_ = lean_ptr_addr(v_k_x27_2443_);
v___x_2446_ = lean_usize_dec_eq(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_unsigned_to_nat(1u);
v___x_2448_ = lean_nat_add(v_i_2438_, v___x_2447_);
lean_dec(v_i_2438_);
v_i_2438_ = v___x_2448_;
goto _start;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_array_fget_borrowed(v_vals_2437_, v_i_2438_);
lean_dec(v_i_2438_);
lean_inc(v___x_2450_);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2452_, lean_object* v_vals_2453_, lean_object* v_i_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2452_, v_vals_2453_, v_i_2454_, v_k_2455_);
lean_dec_ref(v_k_2455_);
lean_dec_ref(v_vals_2453_);
lean_dec_ref(v_keys_2452_);
return v_res_2456_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2457_, size_t v_x_2458_, lean_object* v_x_2459_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 0)
{
lean_object* v_es_2460_; lean_object* v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; lean_object* v_j_2464_; lean_object* v___x_2465_; 
v_es_2460_ = lean_ctor_get(v_x_2457_, 0);
v___x_2461_ = lean_box(2);
v___x_2462_ = ((size_t)31ULL);
v___x_2463_ = lean_usize_land(v_x_2458_, v___x_2462_);
v_j_2464_ = lean_usize_to_nat(v___x_2463_);
v___x_2465_ = lean_array_get_borrowed(v___x_2461_, v_es_2460_, v_j_2464_);
lean_dec(v_j_2464_);
switch(lean_obj_tag(v___x_2465_))
{
case 0:
{
lean_object* v_key_2466_; lean_object* v_val_2467_; size_t v___x_2468_; size_t v___x_2469_; uint8_t v___x_2470_; 
v_key_2466_ = lean_ctor_get(v___x_2465_, 0);
v_val_2467_ = lean_ctor_get(v___x_2465_, 1);
v___x_2468_ = lean_ptr_addr(v_x_2459_);
v___x_2469_ = lean_ptr_addr(v_key_2466_);
v___x_2470_ = lean_usize_dec_eq(v___x_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_box(0);
return v___x_2471_;
}
else
{
lean_object* v___x_2472_; 
lean_inc(v_val_2467_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_val_2467_);
return v___x_2472_;
}
}
case 1:
{
lean_object* v_node_2473_; size_t v___x_2474_; size_t v___x_2475_; 
v_node_2473_ = lean_ctor_get(v___x_2465_, 0);
v___x_2474_ = ((size_t)5ULL);
v___x_2475_ = lean_usize_shift_right(v_x_2458_, v___x_2474_);
v_x_2457_ = v_node_2473_;
v_x_2458_ = v___x_2475_;
goto _start;
}
default: 
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_box(0);
return v___x_2477_;
}
}
}
else
{
lean_object* v_ks_2478_; lean_object* v_vs_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_ks_2478_ = lean_ctor_get(v_x_2457_, 0);
v_vs_2479_ = lean_ctor_get(v_x_2457_, 1);
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2478_, v_vs_2479_, v___x_2480_, v_x_2459_);
return v___x_2481_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2457_ = stack[0].m_obj;
size_t v_x_2458_ = stack[1].m_num;
lean_object* v_x_2459_ = stack[2].m_obj;
lean_object* v_res_2482_;
v_res_2482_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2457_, v_x_2458_, v_x_2459_);
stack->m_obj
 = v_res_2482_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_){
_start:
{
size_t v_x_19752__boxed_2486_; lean_object* v_res_2487_; 
v_x_19752__boxed_2486_ = lean_unbox_usize(v_x_2484_);
lean_dec(v_x_2484_);
v_res_2487_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2483_, v_x_19752__boxed_2486_, v_x_2485_);
lean_dec_ref(v_x_2485_);
lean_dec_ref(v_x_2483_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2488_, lean_object* v_x_2489_){
_start:
{
size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; uint64_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2490_ = lean_ptr_addr(v_x_2489_);
v___x_2491_ = ((size_t)3ULL);
v___x_2492_ = lean_usize_shift_right(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_usize_to_uint64(v___x_2492_);
v___x_2494_ = lean_uint64_to_usize(v___x_2493_);
v___x_2495_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2488_, v___x_2494_, v_x_2489_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2496_, v_x_2497_);
lean_dec_ref(v_x_2497_);
lean_dec_ref(v_x_2496_);
return v_res_2498_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
if (lean_obj_tag(v_as_x27_2499_) == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_b_2500_);
return v___x_2512_;
}
else
{
lean_object* v_head_2513_; lean_object* v_tail_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v_toGoalState_2517_; lean_object* v_ematch_2518_; lean_object* v_delayedThmInsts_2519_; lean_object* v___x_2520_; 
v_head_2513_ = lean_ctor_get(v_as_x27_2499_, 0);
v_tail_2514_ = lean_ctor_get(v_as_x27_2499_, 1);
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_st_ref_get(v___y_2501_);
v_toGoalState_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_ref(v_toGoalState_2517_);
lean_dec(v___x_2516_);
v_ematch_2518_ = lean_ctor_get(v_toGoalState_2517_, 12);
lean_inc_ref(v_ematch_2518_);
lean_dec_ref(v_toGoalState_2517_);
v_delayedThmInsts_2519_ = lean_ctor_get(v_ematch_2518_, 10);
lean_inc_ref(v_delayedThmInsts_2519_);
lean_dec_ref(v_ematch_2518_);
v___x_2520_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2519_, v_head_2513_);
lean_dec_ref(v_delayedThmInsts_2519_);
if (lean_obj_tag(v___x_2520_) == 1)
{
lean_object* v_val_2521_; lean_object* v___x_2522_; lean_object* v_toGoalState_2523_; lean_object* v_ematch_2524_; lean_object* v_mvarId_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2579_; 
v_val_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_val_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = lean_st_ref_take(v___y_2501_);
v_toGoalState_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_toGoalState_2523_);
v_ematch_2524_ = lean_ctor_get(v_toGoalState_2523_, 12);
lean_inc_ref(v_ematch_2524_);
v_mvarId_2525_ = lean_ctor_get(v___x_2522_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2522_, 0);
lean_dec(v_unused_2580_);
v___x_2527_ = v___x_2522_;
v_isShared_2528_ = v_isSharedCheck_2579_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_mvarId_2525_);
lean_dec(v___x_2522_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2579_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_nextDeclIdx_2529_; lean_object* v_enodeMap_2530_; lean_object* v_exprs_2531_; lean_object* v_parents_2532_; lean_object* v_congrTable_2533_; lean_object* v_appMap_2534_; lean_object* v_indicesFound_2535_; lean_object* v_toProcess_2536_; uint8_t v_inconsistent_2537_; lean_object* v_nextIdx_2538_; lean_object* v_newRawFacts_2539_; lean_object* v_facts_2540_; lean_object* v_extThms_2541_; lean_object* v_inj_2542_; lean_object* v_split_2543_; lean_object* v_clean_2544_; lean_object* v_sstates_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2577_; 
v_nextDeclIdx_2529_ = lean_ctor_get(v_toGoalState_2523_, 0);
v_enodeMap_2530_ = lean_ctor_get(v_toGoalState_2523_, 1);
v_exprs_2531_ = lean_ctor_get(v_toGoalState_2523_, 2);
v_parents_2532_ = lean_ctor_get(v_toGoalState_2523_, 3);
v_congrTable_2533_ = lean_ctor_get(v_toGoalState_2523_, 4);
v_appMap_2534_ = lean_ctor_get(v_toGoalState_2523_, 5);
v_indicesFound_2535_ = lean_ctor_get(v_toGoalState_2523_, 6);
v_toProcess_2536_ = lean_ctor_get(v_toGoalState_2523_, 7);
v_inconsistent_2537_ = lean_ctor_get_uint8(v_toGoalState_2523_, sizeof(void*)*17);
v_nextIdx_2538_ = lean_ctor_get(v_toGoalState_2523_, 8);
v_newRawFacts_2539_ = lean_ctor_get(v_toGoalState_2523_, 9);
v_facts_2540_ = lean_ctor_get(v_toGoalState_2523_, 10);
v_extThms_2541_ = lean_ctor_get(v_toGoalState_2523_, 11);
v_inj_2542_ = lean_ctor_get(v_toGoalState_2523_, 13);
v_split_2543_ = lean_ctor_get(v_toGoalState_2523_, 14);
v_clean_2544_ = lean_ctor_get(v_toGoalState_2523_, 15);
v_sstates_2545_ = lean_ctor_get(v_toGoalState_2523_, 16);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_toGoalState_2523_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v_toGoalState_2523_, 12);
lean_dec(v_unused_2578_);
v___x_2547_ = v_toGoalState_2523_;
v_isShared_2548_ = v_isSharedCheck_2577_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_sstates_2545_);
lean_inc(v_clean_2544_);
lean_inc(v_split_2543_);
lean_inc(v_inj_2542_);
lean_inc(v_extThms_2541_);
lean_inc(v_facts_2540_);
lean_inc(v_newRawFacts_2539_);
lean_inc(v_nextIdx_2538_);
lean_inc(v_toProcess_2536_);
lean_inc(v_indicesFound_2535_);
lean_inc(v_appMap_2534_);
lean_inc(v_congrTable_2533_);
lean_inc(v_parents_2532_);
lean_inc(v_exprs_2531_);
lean_inc(v_enodeMap_2530_);
lean_inc(v_nextDeclIdx_2529_);
lean_dec(v_toGoalState_2523_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2577_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_thmMap_2549_; lean_object* v_gmt_2550_; lean_object* v_thms_2551_; lean_object* v_newThms_2552_; lean_object* v_numInstances_2553_; lean_object* v_numDelayedInstances_2554_; lean_object* v_num_2555_; lean_object* v_preInstances_2556_; lean_object* v_nextThmIdx_2557_; lean_object* v_matchEqNames_2558_; lean_object* v_delayedThmInsts_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2576_; 
v_thmMap_2549_ = lean_ctor_get(v_ematch_2524_, 0);
v_gmt_2550_ = lean_ctor_get(v_ematch_2524_, 1);
v_thms_2551_ = lean_ctor_get(v_ematch_2524_, 2);
v_newThms_2552_ = lean_ctor_get(v_ematch_2524_, 3);
v_numInstances_2553_ = lean_ctor_get(v_ematch_2524_, 4);
v_numDelayedInstances_2554_ = lean_ctor_get(v_ematch_2524_, 5);
v_num_2555_ = lean_ctor_get(v_ematch_2524_, 6);
v_preInstances_2556_ = lean_ctor_get(v_ematch_2524_, 7);
v_nextThmIdx_2557_ = lean_ctor_get(v_ematch_2524_, 8);
v_matchEqNames_2558_ = lean_ctor_get(v_ematch_2524_, 9);
v_delayedThmInsts_2559_ = lean_ctor_get(v_ematch_2524_, 10);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_ematch_2524_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2561_ = v_ematch_2524_;
v_isShared_2562_ = v_isSharedCheck_2576_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_delayedThmInsts_2559_);
lean_inc(v_matchEqNames_2558_);
lean_inc(v_nextThmIdx_2557_);
lean_inc(v_preInstances_2556_);
lean_inc(v_num_2555_);
lean_inc(v_numDelayedInstances_2554_);
lean_inc(v_numInstances_2553_);
lean_inc(v_newThms_2552_);
lean_inc(v_thms_2551_);
lean_inc(v_gmt_2550_);
lean_inc(v_thmMap_2549_);
lean_dec(v_ematch_2524_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2576_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2563_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2559_, v_head_2513_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 10, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_thmMap_2549_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_gmt_2550_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_thms_2551_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_newThms_2552_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_numInstances_2553_);
lean_ctor_set(v_reuseFailAlloc_2575_, 5, v_numDelayedInstances_2554_);
lean_ctor_set(v_reuseFailAlloc_2575_, 6, v_num_2555_);
lean_ctor_set(v_reuseFailAlloc_2575_, 7, v_preInstances_2556_);
lean_ctor_set(v_reuseFailAlloc_2575_, 8, v_nextThmIdx_2557_);
lean_ctor_set(v_reuseFailAlloc_2575_, 9, v_matchEqNames_2558_);
lean_ctor_set(v_reuseFailAlloc_2575_, 10, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 12, v___x_2565_);
v___x_2567_ = v___x_2547_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_nextDeclIdx_2529_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_enodeMap_2530_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_exprs_2531_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v_parents_2532_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_congrTable_2533_);
lean_ctor_set(v_reuseFailAlloc_2574_, 5, v_appMap_2534_);
lean_ctor_set(v_reuseFailAlloc_2574_, 6, v_indicesFound_2535_);
lean_ctor_set(v_reuseFailAlloc_2574_, 7, v_toProcess_2536_);
lean_ctor_set(v_reuseFailAlloc_2574_, 8, v_nextIdx_2538_);
lean_ctor_set(v_reuseFailAlloc_2574_, 9, v_newRawFacts_2539_);
lean_ctor_set(v_reuseFailAlloc_2574_, 10, v_facts_2540_);
lean_ctor_set(v_reuseFailAlloc_2574_, 11, v_extThms_2541_);
lean_ctor_set(v_reuseFailAlloc_2574_, 12, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2574_, 13, v_inj_2542_);
lean_ctor_set(v_reuseFailAlloc_2574_, 14, v_split_2543_);
lean_ctor_set(v_reuseFailAlloc_2574_, 15, v_clean_2544_);
lean_ctor_set(v_reuseFailAlloc_2574_, 16, v_sstates_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2574_, sizeof(void*)*17, v_inconsistent_2537_);
v___x_2567_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2567_);
v___x_2569_ = v___x_2527_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_mvarId_2525_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_st_ref_put(v___y_2501_, v___x_2569_);
v___x_2571_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2521_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_dec_ref_known(v___x_2571_, 1);
v_as_x27_2499_ = v_tail_2514_;
v_b_2500_ = v___x_2515_;
goto _start;
}
else
{
return v___x_2571_;
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
lean_dec(v___x_2520_);
v_as_x27_2499_ = v_tail_2514_;
v_b_2500_ = v___x_2515_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2499_ = stack[0].m_obj;
lean_object* v_b_2500_ = stack[1].m_obj;
lean_object* v___y_2501_ = stack[2].m_obj;
lean_object* v___y_2502_ = stack[3].m_obj;
lean_object* v___y_2503_ = stack[4].m_obj;
lean_object* v___y_2504_ = stack[5].m_obj;
lean_object* v___y_2505_ = stack[6].m_obj;
lean_object* v___y_2506_ = stack[7].m_obj;
lean_object* v___y_2507_ = stack[8].m_obj;
lean_object* v___y_2508_ = stack[9].m_obj;
lean_object* v___y_2509_ = stack[10].m_obj;
lean_object* v___y_2510_ = stack[11].m_obj;
lean_object* v_res_2582_;
v_res_2582_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2499_, v_b_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
stack->m_obj
 = v_res_2582_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2583_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v_as_x27_2583_);
return v_res_2596_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2598_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2638_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2638_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2638_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_unbox(v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v_toGoalState_2616_; lean_object* v_ematch_2617_; lean_object* v_delayedThmInsts_2618_; uint8_t v___x_2619_; 
v___x_2615_ = lean_st_ref_get(v_a_2598_);
v_toGoalState_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc_ref(v_toGoalState_2616_);
lean_dec(v___x_2615_);
v_ematch_2617_ = lean_ctor_get(v_toGoalState_2616_, 12);
lean_inc_ref(v_ematch_2617_);
lean_dec_ref(v_toGoalState_2616_);
v_delayedThmInsts_2618_ = lean_ctor_get(v_ematch_2617_, 10);
lean_inc_ref(v_delayedThmInsts_2618_);
lean_dec_ref(v_ematch_2617_);
v___x_2619_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2618_);
lean_dec_ref(v_delayedThmInsts_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_del_object(v___x_2612_);
v___x_2620_ = lean_box(0);
v___x_2621_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2597_, v___x_2620_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2629_);
v___x_2623_ = v___x_2621_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_dec(v___x_2621_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2620_);
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2620_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = lean_box(0);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2630_);
v___x_2632_ = v___x_2612_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_box(0);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2634_);
v___x_2636_ = v___x_2612_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2609_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2609_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPropagateDown_2597_ = stack[0].m_obj;
lean_object* v_a_2598_ = stack[1].m_obj;
lean_object* v_a_2599_ = stack[2].m_obj;
lean_object* v_a_2600_ = stack[3].m_obj;
lean_object* v_a_2601_ = stack[4].m_obj;
lean_object* v_a_2602_ = stack[5].m_obj;
lean_object* v_a_2603_ = stack[6].m_obj;
lean_object* v_a_2604_ = stack[7].m_obj;
lean_object* v_a_2605_ = stack[8].m_obj;
lean_object* v_a_2606_ = stack[9].m_obj;
lean_object* v_a_2607_ = stack[10].m_obj;
lean_object* v_res_2647_;
v_res_2647_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
stack->m_obj
 = v_res_2647_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_toPropagateDown_2648_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2665_, v_x_2666_, v_x_2667_);
lean_dec_ref(v_x_2667_);
lean_dec_ref(v_x_2666_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2670_, v_x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2673_, v_x_2674_, v_x_2675_);
lean_dec_ref(v_x_2675_);
return v_res_2676_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2677_, lean_object* v_as_x27_2678_, lean_object* v_b_2679_, lean_object* v_a_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2678_, v_b_2679_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2677_ = stack[0].m_obj;
lean_object* v_as_x27_2678_ = stack[1].m_obj;
lean_object* v_b_2679_ = stack[2].m_obj;
lean_object* v___y_2681_ = stack[4].m_obj;
lean_object* v___y_2682_ = stack[5].m_obj;
lean_object* v___y_2683_ = stack[6].m_obj;
lean_object* v___y_2684_ = stack[7].m_obj;
lean_object* v___y_2685_ = stack[8].m_obj;
lean_object* v___y_2686_ = stack[9].m_obj;
lean_object* v___y_2687_ = stack[10].m_obj;
lean_object* v___y_2688_ = stack[11].m_obj;
lean_object* v___y_2689_ = stack[12].m_obj;
lean_object* v___y_2690_ = stack[13].m_obj;
lean_object* v_res_2693_;
v_res_2693_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2677_, v_as_x27_2678_, v_b_2679_, lean_box(0), v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
stack->m_obj
 = v_res_2693_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2694_, lean_object* v_as_x27_2695_, lean_object* v_b_2696_, lean_object* v_a_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2694_, v_as_x27_2695_, v_b_2696_, v_a_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v_as_x27_2695_);
lean_dec(v_as_2694_);
return v_res_2709_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2710_, lean_object* v_x_2711_, size_t v_x_2712_, lean_object* v_x_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2711_, v_x_2712_, v_x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2711_ = stack[1].m_obj;
size_t v_x_2712_ = stack[2].m_num;
lean_object* v_x_2713_ = stack[3].m_obj;
lean_object* v_res_2715_;
v_res_2715_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_box(0), v_x_2711_, v_x_2712_, v_x_2713_);
stack->m_obj
 = v_res_2715_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
size_t v_x_20224__boxed_2720_; lean_object* v_res_2721_; 
v_x_20224__boxed_2720_ = lean_unbox_usize(v_x_2718_);
lean_dec(v_x_2718_);
v_res_2721_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2716_, v_x_2717_, v_x_20224__boxed_2720_, v_x_2719_);
lean_dec_ref(v_x_2719_);
lean_dec_ref(v_x_2717_);
return v_res_2721_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2722_, lean_object* v_x_2723_, size_t v_x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2723_, v_x_2724_, v_x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2723_ = stack[1].m_obj;
size_t v_x_2724_ = stack[2].m_num;
lean_object* v_x_2725_ = stack[3].m_obj;
lean_object* v_res_2727_;
v_res_2727_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_box(0), v_x_2723_, v_x_2724_, v_x_2725_);
stack->m_obj
 = v_res_2727_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v_x_2731_){
_start:
{
size_t v_x_20242__boxed_2732_; lean_object* v_res_2733_; 
v_x_20242__boxed_2732_ = lean_unbox_usize(v_x_2730_);
lean_dec(v_x_2730_);
v_res_2733_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2728_, v_x_2729_, v_x_20242__boxed_2732_, v_x_2731_);
lean_dec_ref(v_x_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2734_, lean_object* v_keys_2735_, lean_object* v_vals_2736_, lean_object* v_heq_2737_, lean_object* v_i_2738_, lean_object* v_k_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2735_, v_vals_2736_, v_i_2738_, v_k_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2741_, lean_object* v_keys_2742_, lean_object* v_vals_2743_, lean_object* v_heq_2744_, lean_object* v_i_2745_, lean_object* v_k_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2741_, v_keys_2742_, v_vals_2743_, v_heq_2744_, v_i_2745_, v_k_2746_);
lean_dec_ref(v_k_2746_);
lean_dec_ref(v_vals_2743_);
lean_dec_ref(v_keys_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2748_, lean_object* v_keys_2749_, lean_object* v_vals_2750_, lean_object* v_i_2751_, lean_object* v_k_2752_){
_start:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = lean_array_get_size(v_keys_2749_);
v___x_2754_ = lean_nat_dec_lt(v_i_2751_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
lean_dec_ref(v_k_2752_);
lean_dec(v_i_2751_);
v___x_2755_ = lean_box(0);
return v___x_2755_;
}
else
{
lean_object* v_k_x27_2756_; uint8_t v___x_2757_; 
v_k_x27_2756_ = lean_array_fget_borrowed(v_keys_2749_, v_i_2751_);
lean_inc(v_k_x27_2756_);
lean_inc_ref(v_k_2752_);
v___x_2757_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2748_, v_k_2752_, v_k_x27_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_unsigned_to_nat(1u);
v___x_2759_ = lean_nat_add(v_i_2751_, v___x_2758_);
lean_dec(v_i_2751_);
v_i_2751_ = v___x_2759_;
goto _start;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v_k_2752_);
v___x_2761_ = lean_array_fget_borrowed(v_vals_2750_, v_i_2751_);
lean_dec(v_i_2751_);
lean_inc(v___x_2761_);
lean_inc(v_k_x27_2756_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_k_x27_2756_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2764_, lean_object* v_keys_2765_, lean_object* v_vals_2766_, lean_object* v_i_2767_, lean_object* v_k_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2764_, v_keys_2765_, v_vals_2766_, v_i_2767_, v_k_2768_);
lean_dec_ref(v_vals_2766_);
lean_dec_ref(v_keys_2765_);
lean_dec_ref(v___x_2764_);
return v_res_2769_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2770_, lean_object* v_x_2771_, size_t v_x_2772_, lean_object* v_x_2773_){
_start:
{
if (lean_obj_tag(v_x_2771_) == 0)
{
lean_object* v_es_2774_; lean_object* v___x_2775_; size_t v___x_2776_; size_t v___x_2777_; lean_object* v_j_2778_; lean_object* v___x_2779_; 
v_es_2774_ = lean_ctor_get(v_x_2771_, 0);
lean_inc_ref(v_es_2774_);
lean_dec_ref_known(v_x_2771_, 1);
v___x_2775_ = lean_box(2);
v___x_2776_ = ((size_t)31ULL);
v___x_2777_ = lean_usize_land(v_x_2772_, v___x_2776_);
v_j_2778_ = lean_usize_to_nat(v___x_2777_);
v___x_2779_ = lean_array_get(v___x_2775_, v_es_2774_, v_j_2778_);
lean_dec(v_j_2778_);
lean_dec_ref(v_es_2774_);
switch(lean_obj_tag(v___x_2779_))
{
case 0:
{
lean_object* v_key_2780_; lean_object* v_val_2781_; uint8_t v___x_2782_; 
v_key_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_n(v_key_2780_, 2);
v_val_2781_ = lean_ctor_get(v___x_2779_, 1);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___x_2779_, 2);
v___x_2782_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2770_, v_x_2773_, v_key_2780_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
lean_dec(v_val_2781_);
lean_dec(v_key_2780_);
v___x_2783_ = lean_box(0);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_key_2780_);
lean_ctor_set(v___x_2784_, 1, v_val_2781_);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
case 1:
{
lean_object* v_node_2786_; size_t v___x_2787_; size_t v___x_2788_; 
v_node_2786_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_node_2786_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2787_ = ((size_t)5ULL);
v___x_2788_ = lean_usize_shift_right(v_x_2772_, v___x_2787_);
v_x_2771_ = v_node_2786_;
v_x_2772_ = v___x_2788_;
goto _start;
}
default: 
{
lean_object* v___x_2790_; 
lean_dec_ref(v_x_2773_);
v___x_2790_ = lean_box(0);
return v___x_2790_;
}
}
}
else
{
lean_object* v_ks_2791_; lean_object* v_vs_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_ks_2791_ = lean_ctor_get(v_x_2771_, 0);
lean_inc_ref(v_ks_2791_);
v_vs_2792_ = lean_ctor_get(v_x_2771_, 1);
lean_inc_ref(v_vs_2792_);
lean_dec_ref_known(v_x_2771_, 2);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2770_, v_ks_2791_, v_vs_2792_, v___x_2793_, v_x_2773_);
lean_dec_ref(v_vs_2792_);
lean_dec_ref(v_ks_2791_);
return v___x_2794_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2770_ = stack[0].m_obj;
lean_object* v_x_2771_ = stack[1].m_obj;
size_t v_x_2772_ = stack[2].m_num;
lean_object* v_x_2773_ = stack[3].m_obj;
lean_object* v_res_2795_;
v_res_2795_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2770_, v_x_2771_, v_x_2772_, v_x_2773_);
stack->m_obj
 = v_res_2795_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2796_, lean_object* v_x_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_){
_start:
{
size_t v_x_25963__boxed_2800_; lean_object* v_res_2801_; 
v_x_25963__boxed_2800_ = lean_unbox_usize(v_x_2798_);
lean_dec(v_x_2798_);
v_res_2801_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2796_, v_x_2797_, v_x_25963__boxed_2800_, v_x_2799_);
lean_dec_ref(v___x_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
uint64_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
lean_inc_ref(v_x_2804_);
v___x_2805_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2802_, v_x_2804_);
v___x_2806_ = lean_uint64_to_usize(v___x_2805_);
lean_inc_ref(v_x_2803_);
v___x_2807_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2802_, v_x_2803_, v___x_2806_, v_x_2804_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2808_, v_x_2809_, v_x_2810_);
lean_dec_ref(v_x_2809_);
lean_dec_ref(v___x_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_){
_start:
{
lean_object* v_ks_2817_; lean_object* v_vs_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2842_; 
v_ks_2817_ = lean_ctor_get(v_x_2813_, 0);
v_vs_2818_ = lean_ctor_get(v_x_2813_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_x_2813_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2820_ = v_x_2813_;
v_isShared_2821_ = v_isSharedCheck_2842_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_vs_2818_);
lean_inc(v_ks_2817_);
lean_dec(v_x_2813_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2842_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = lean_array_get_size(v_ks_2817_);
v___x_2823_ = lean_nat_dec_lt(v_x_2814_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_dec(v_x_2814_);
v___x_2824_ = lean_array_push(v_ks_2817_, v_x_2815_);
v___x_2825_ = lean_array_push(v_vs_2818_, v_x_2816_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 1, v___x_2825_);
lean_ctor_set(v___x_2820_, 0, v___x_2824_);
v___x_2827_ = v___x_2820_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
lean_object* v_k_x27_2829_; uint8_t v___x_2830_; 
v_k_x27_2829_ = lean_array_fget_borrowed(v_ks_2817_, v_x_2814_);
lean_inc(v_k_x27_2829_);
lean_inc_ref(v_x_2815_);
v___x_2830_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2812_, v_x_2815_, v_k_x27_2829_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2832_; 
if (v_isShared_2821_ == 0)
{
v___x_2832_ = v___x_2820_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_ks_2817_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_vs_2818_);
v___x_2832_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_x_2814_, v___x_2833_);
lean_dec(v_x_2814_);
v_x_2813_ = v___x_2832_;
v_x_2814_ = v___x_2834_;
goto _start;
}
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2837_ = lean_array_fset(v_ks_2817_, v_x_2814_, v_x_2815_);
v___x_2838_ = lean_array_fset(v_vs_2818_, v_x_2814_, v_x_2816_);
lean_dec(v_x_2814_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 1, v___x_2838_);
lean_ctor_set(v___x_2820_, 0, v___x_2837_);
v___x_2840_ = v___x_2820_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2843_, v_x_2844_, v_x_2845_, v_x_2846_, v_x_2847_);
lean_dec_ref(v___x_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2849_, lean_object* v_n_2850_, lean_object* v_k_2851_, lean_object* v_v_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2849_, v_n_2850_, v___x_2853_, v_k_2851_, v_v_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2855_, lean_object* v_n_2856_, lean_object* v_k_2857_, lean_object* v_v_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2855_, v_n_2856_, v_k_2857_, v_v_2858_);
lean_dec_ref(v___x_2855_);
return v_res_2859_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2860_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2861_, lean_object* v_x_2862_, size_t v_x_2863_, size_t v_x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2862_) == 0)
{
lean_object* v_es_2867_; size_t v___x_2868_; size_t v___x_2869_; lean_object* v_j_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_es_2867_ = lean_ctor_get(v_x_2862_, 0);
v___x_2868_ = ((size_t)31ULL);
v___x_2869_ = lean_usize_land(v_x_2863_, v___x_2868_);
v_j_2870_ = lean_usize_to_nat(v___x_2869_);
v___x_2871_ = lean_array_get_size(v_es_2867_);
v___x_2872_ = lean_nat_dec_lt(v_j_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_dec(v_j_2870_);
lean_dec(v_x_2866_);
lean_dec_ref(v_x_2865_);
return v_x_2862_;
}
else
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2911_; 
lean_inc_ref(v_es_2867_);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; 
v_unused_2912_ = lean_ctor_get(v_x_2862_, 0);
lean_dec(v_unused_2912_);
v___x_2874_ = v_x_2862_;
v_isShared_2875_ = v_isSharedCheck_2911_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v_x_2862_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2911_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_v_2876_; lean_object* v___x_2877_; lean_object* v_xs_x27_2878_; lean_object* v___y_2880_; 
v_v_2876_ = lean_array_fget(v_es_2867_, v_j_2870_);
v___x_2877_ = lean_box(0);
v_xs_x27_2878_ = lean_array_fset(v_es_2867_, v_j_2870_, v___x_2877_);
switch(lean_obj_tag(v_v_2876_))
{
case 0:
{
lean_object* v_key_2885_; lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2896_; 
v_key_2885_ = lean_ctor_get(v_v_2876_, 0);
v_val_2886_ = lean_ctor_get(v_v_2876_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_v_2876_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2888_ = v_v_2876_;
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_inc(v_key_2885_);
lean_dec(v_v_2876_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2896_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint8_t v___x_2890_; 
lean_inc(v_key_2885_);
lean_inc_ref(v_x_2865_);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2861_, v_x_2865_, v_key_2885_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_del_object(v___x_2888_);
v___x_2891_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2885_, v_val_2886_, v_x_2865_, v_x_2866_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___y_2880_ = v___x_2892_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2894_; 
lean_dec(v_val_2886_);
lean_dec(v_key_2885_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v_x_2866_);
lean_ctor_set(v___x_2888_, 0, v_x_2865_);
v___x_2894_ = v___x_2888_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_x_2865_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_x_2866_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v___y_2880_ = v___x_2894_;
goto v___jp_2879_;
}
}
}
}
case 1:
{
lean_object* v_node_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2909_; 
v_node_2897_ = lean_ctor_get(v_v_2876_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_v_2876_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2899_ = v_v_2876_;
v_isShared_2900_ = v_isSharedCheck_2909_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_node_2897_);
lean_dec(v_v_2876_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2909_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
size_t v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2901_ = ((size_t)5ULL);
v___x_2902_ = lean_usize_shift_right(v_x_2863_, v___x_2901_);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_x_2864_, v___x_2903_);
v___x_2905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2861_, v_node_2897_, v___x_2902_, v___x_2904_, v_x_2865_, v_x_2866_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2905_);
v___x_2907_ = v___x_2899_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
v___y_2880_ = v___x_2907_;
goto v___jp_2879_;
}
}
}
default: 
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_x_2865_);
lean_ctor_set(v___x_2910_, 1, v_x_2866_);
v___y_2880_ = v___x_2910_;
goto v___jp_2879_;
}
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_array_fset(v_xs_x27_2878_, v_j_2870_, v___y_2880_);
lean_dec(v_j_2870_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2881_);
v___x_2883_ = v___x_2874_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v_ks_2913_; lean_object* v_vs_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2932_; 
v_ks_2913_ = lean_ctor_get(v_x_2862_, 0);
v_vs_2914_ = lean_ctor_get(v_x_2862_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2916_ = v_x_2862_;
v_isShared_2917_ = v_isSharedCheck_2932_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_vs_2914_);
lean_inc(v_ks_2913_);
lean_dec(v_x_2862_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2932_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_ks_2913_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_vs_2914_);
v___x_2919_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v_newNode_2920_; size_t v___x_2921_; uint8_t v___x_2922_; 
v_newNode_2920_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2861_, v___x_2919_, v_x_2865_, v_x_2866_);
v___x_2921_ = ((size_t)7ULL);
v___x_2922_ = lean_usize_dec_le(v___x_2921_, v_x_2864_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2920_);
v___x_2924_ = lean_unsigned_to_nat(4u);
v___x_2925_ = lean_nat_dec_lt(v___x_2923_, v___x_2924_);
lean_dec(v___x_2923_);
if (v___x_2925_ == 0)
{
lean_object* v_ks_2926_; lean_object* v_vs_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_ks_2926_ = lean_ctor_get(v_newNode_2920_, 0);
lean_inc_ref(v_ks_2926_);
v_vs_2927_ = lean_ctor_get(v_newNode_2920_, 1);
lean_inc_ref(v_vs_2927_);
lean_dec_ref(v_newNode_2920_);
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2861_, v_x_2864_, v_ks_2926_, v_vs_2927_, v___x_2928_, v___x_2929_);
lean_dec_ref(v_vs_2927_);
lean_dec_ref(v_ks_2926_);
return v___x_2930_;
}
else
{
return v_newNode_2920_;
}
}
else
{
return v_newNode_2920_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2861_ = stack[0].m_obj;
lean_object* v_x_2862_ = stack[1].m_obj;
size_t v_x_2863_ = stack[2].m_num;
size_t v_x_2864_ = stack[3].m_num;
lean_object* v_x_2865_ = stack[4].m_obj;
lean_object* v_x_2866_ = stack[5].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2861_, v_x_2862_, v_x_2863_, v_x_2864_, v_x_2865_, v_x_2866_);
stack->m_obj
 = v_res_2933_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2934_, size_t v_depth_2935_, lean_object* v_keys_2936_, lean_object* v_vals_2937_, lean_object* v_i_2938_, lean_object* v_entries_2939_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_keys_2936_);
v___x_2941_ = lean_nat_dec_lt(v_i_2938_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec(v_i_2938_);
return v_entries_2939_;
}
else
{
lean_object* v_k_2942_; lean_object* v_v_2943_; uint64_t v___x_2944_; size_t v_h_2945_; size_t v___x_2946_; lean_object* v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; size_t v_h_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_k_2942_ = lean_array_fget_borrowed(v_keys_2936_, v_i_2938_);
v_v_2943_ = lean_array_fget_borrowed(v_vals_2937_, v_i_2938_);
lean_inc_n(v_k_2942_, 2);
v___x_2944_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2934_, v_k_2942_);
v_h_2945_ = lean_uint64_to_usize(v___x_2944_);
v___x_2946_ = ((size_t)5ULL);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_sub(v_depth_2935_, v___x_2948_);
v___x_2950_ = lean_usize_mul(v___x_2946_, v___x_2949_);
v_h_2951_ = lean_usize_shift_right(v_h_2945_, v___x_2950_);
v___x_2952_ = lean_nat_add(v_i_2938_, v___x_2947_);
lean_dec(v_i_2938_);
lean_inc(v_v_2943_);
v___x_2953_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2934_, v_entries_2939_, v_h_2951_, v_depth_2935_, v_k_2942_, v_v_2943_);
v_i_2938_ = v___x_2952_;
v_entries_2939_ = v___x_2953_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2934_ = stack[0].m_obj;
size_t v_depth_2935_ = stack[1].m_num;
lean_object* v_keys_2936_ = stack[2].m_obj;
lean_object* v_vals_2937_ = stack[3].m_obj;
lean_object* v_i_2938_ = stack[4].m_obj;
lean_object* v_entries_2939_ = stack[5].m_obj;
lean_object* v_res_2955_;
v_res_2955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2934_, v_depth_2935_, v_keys_2936_, v_vals_2937_, v_i_2938_, v_entries_2939_);
stack->m_obj
 = v_res_2955_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2956_, lean_object* v_depth_2957_, lean_object* v_keys_2958_, lean_object* v_vals_2959_, lean_object* v_i_2960_, lean_object* v_entries_2961_){
_start:
{
size_t v_depth_boxed_2962_; lean_object* v_res_2963_; 
v_depth_boxed_2962_ = lean_unbox_usize(v_depth_2957_);
lean_dec(v_depth_2957_);
v_res_2963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2956_, v_depth_boxed_2962_, v_keys_2958_, v_vals_2959_, v_i_2960_, v_entries_2961_);
lean_dec_ref(v_vals_2959_);
lean_dec_ref(v_keys_2958_);
lean_dec_ref(v___x_2956_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
size_t v_x_26193__boxed_2970_; size_t v_x_26194__boxed_2971_; lean_object* v_res_2972_; 
v_x_26193__boxed_2970_ = lean_unbox_usize(v_x_2966_);
lean_dec(v_x_2966_);
v_x_26194__boxed_2971_ = lean_unbox_usize(v_x_2967_);
lean_dec(v_x_2967_);
v_res_2972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2964_, v_x_2965_, v_x_26193__boxed_2970_, v_x_26194__boxed_2971_, v_x_2968_, v_x_2969_);
lean_dec_ref(v___x_2964_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_, lean_object* v_x_2976_){
_start:
{
uint64_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; lean_object* v___x_2980_; 
lean_inc_ref(v_x_2975_);
v___x_2977_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2973_, v_x_2975_);
v___x_2978_ = lean_uint64_to_usize(v___x_2977_);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2973_, v_x_2974_, v___x_2978_, v___x_2979_, v_x_2975_, v_x_2976_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2981_, v_x_2982_, v_x_2983_, v_x_2984_);
lean_dec_ref(v___x_2981_);
return v_res_2985_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2990_, lean_object* v_rootNew_2991_, uint8_t v_a_2992_, lean_object* v_a_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_snd_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3171_; 
v_snd_3001_ = lean_ctor_get(v_a_2993_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_a_2993_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_a_2993_, 0);
lean_dec(v_unused_3172_);
v___x_3003_ = v_a_2993_;
v_isShared_3004_ = v_isSharedCheck_3171_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_snd_3001_);
lean_dec(v_a_2993_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3171_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_st_ref_get(v___y_2994_);
lean_inc(v_snd_3001_);
v___x_3007_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3006_, v_snd_3001_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3162_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3162_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3162_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v_self_3012_; lean_object* v_next_3013_; lean_object* v_congr_3014_; lean_object* v_target_x3f_3015_; lean_object* v_proof_x3f_3016_; uint8_t v_flipped_3017_; lean_object* v_size_3018_; uint8_t v_interpreted_3019_; uint8_t v_ctor_3020_; uint8_t v_hasLambdas_3021_; uint8_t v_heqProofs_3022_; lean_object* v_idx_3023_; lean_object* v_generation_3024_; lean_object* v_mt_3025_; lean_object* v_sTerms_3026_; uint8_t v_funCC_3027_; lean_object* v_ematchDiagSource_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3160_; 
v_self_3012_ = lean_ctor_get(v_a_3008_, 0);
v_next_3013_ = lean_ctor_get(v_a_3008_, 1);
v_congr_3014_ = lean_ctor_get(v_a_3008_, 3);
v_target_x3f_3015_ = lean_ctor_get(v_a_3008_, 4);
v_proof_x3f_3016_ = lean_ctor_get(v_a_3008_, 5);
v_flipped_3017_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12);
v_size_3018_ = lean_ctor_get(v_a_3008_, 6);
v_interpreted_3019_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12 + 1);
v_ctor_3020_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12 + 2);
v_hasLambdas_3021_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12 + 3);
v_heqProofs_3022_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12 + 4);
v_idx_3023_ = lean_ctor_get(v_a_3008_, 7);
v_generation_3024_ = lean_ctor_get(v_a_3008_, 8);
v_mt_3025_ = lean_ctor_get(v_a_3008_, 9);
v_sTerms_3026_ = lean_ctor_get(v_a_3008_, 10);
v_funCC_3027_ = lean_ctor_get_uint8(v_a_3008_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3028_ = lean_ctor_get(v_a_3008_, 11);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_a_3008_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_a_3008_, 2);
lean_dec(v_unused_3161_);
v___x_3030_ = v_a_3008_;
v_isShared_3031_ = v_isSharedCheck_3160_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_ematchDiagSource_3028_);
lean_inc(v_sTerms_3026_);
lean_inc(v_mt_3025_);
lean_inc(v_generation_3024_);
lean_inc(v_idx_3023_);
lean_inc(v_size_3018_);
lean_inc(v_proof_x3f_3016_);
lean_inc(v_target_x3f_3015_);
lean_inc(v_congr_3014_);
lean_inc(v_next_3013_);
lean_inc(v_self_3012_);
lean_dec(v_a_3008_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3160_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___y_3048_; lean_object* v___x_3058_; 
lean_inc(v_ematchDiagSource_3028_);
lean_inc(v_sTerms_3026_);
lean_inc(v_mt_3025_);
lean_inc(v_generation_3024_);
lean_inc(v_idx_3023_);
lean_inc(v_size_3018_);
lean_inc(v_proof_x3f_3016_);
lean_inc(v_target_x3f_3015_);
lean_inc_ref(v_rootNew_2991_);
lean_inc_ref(v_next_3013_);
lean_inc_ref(v_self_3012_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 2, v_rootNew_2991_);
v___x_3058_ = v___x_3030_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_self_3012_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_next_3013_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_rootNew_2991_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_congr_3014_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_target_x3f_3015_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_proof_x3f_3016_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_size_3018_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_idx_3023_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_generation_3024_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v_mt_3025_);
lean_ctor_set(v_reuseFailAlloc_3159_, 10, v_sTerms_3026_);
lean_ctor_set(v_reuseFailAlloc_3159_, 11, v_ematchDiagSource_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12, v_flipped_3017_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12 + 1, v_interpreted_3019_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12 + 2, v_ctor_3020_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12 + 3, v_hasLambdas_3021_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12 + 4, v_heqProofs_3022_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*12 + 5, v_funCC_3027_);
v___x_3058_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3057_;
}
v___jp_3032_:
{
size_t v___x_3033_; size_t v___x_3034_; uint8_t v___x_3035_; 
v___x_3033_ = lean_ptr_addr(v_next_3013_);
v___x_3034_ = lean_ptr_addr(v_lhs_2990_);
v___x_3035_ = lean_usize_dec_eq(v___x_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3037_; 
lean_del_object(v___x_3010_);
lean_dec(v_snd_3001_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v_next_3013_);
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3037_ = v___x_3003_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_next_3013_);
v___x_3037_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
v_a_2993_ = v___x_3037_;
goto _start;
}
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3042_; 
lean_dec_ref(v_next_3013_);
lean_dec_ref(v_rootNew_2991_);
v___x_3040_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3040_);
v___x_3042_ = v___x_3003_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_snd_3001_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3044_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3042_);
v___x_3044_ = v___x_3010_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
v___jp_3047_:
{
if (lean_obj_tag(v___y_3048_) == 0)
{
lean_dec_ref_known(v___y_3048_, 1);
goto v___jp_3032_;
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_next_3013_);
lean_del_object(v___x_3010_);
lean_del_object(v___x_3003_);
lean_dec(v_snd_3001_);
lean_dec_ref(v_rootNew_2991_);
v_a_3049_ = lean_ctor_get(v___y_3048_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___y_3048_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___y_3048_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___y_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; 
lean_inc_ref(v___x_3058_);
lean_inc_ref(v_self_3012_);
v___x_3059_ = l_Lean_Meta_Grind_setENode___redArg(v_self_3012_, v___x_3058_, v___y_2994_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
if (v_a_2992_ == 0)
{
lean_dec_ref(v___x_3058_);
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
goto v___jp_3032_;
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3060_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3061_ = lean_unsigned_to_nat(3u);
v___x_3062_ = l_Lean_Expr_isAppOfArity(v_self_3012_, v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3058_);
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
goto v___jp_3032_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3058_);
lean_dec_ref(v___x_3058_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v_toGoalState_3065_; lean_object* v_enodeMap_3066_; lean_object* v_congrTable_3067_; lean_object* v___x_3068_; 
v___x_3064_ = lean_st_ref_get(v___y_2994_);
v_toGoalState_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc_ref(v_toGoalState_3065_);
lean_dec(v___x_3064_);
v_enodeMap_3066_ = lean_ctor_get(v_toGoalState_3065_, 1);
lean_inc_ref(v_enodeMap_3066_);
v_congrTable_3067_ = lean_ctor_get(v_toGoalState_3065_, 4);
lean_inc_ref(v_congrTable_3067_);
lean_dec_ref(v_toGoalState_3065_);
lean_inc_ref(v_self_3012_);
v___x_3068_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3066_, v_congrTable_3067_, v_self_3012_);
lean_dec_ref(v_congrTable_3067_);
lean_dec_ref(v_enodeMap_3066_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
goto v___jp_3032_;
}
else
{
lean_object* v_val_3069_; lean_object* v_fst_3070_; lean_object* v___x_3071_; 
v_val_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v_fst_3070_ = lean_ctor_get(v_val_3069_, 0);
lean_inc(v_fst_3070_);
lean_dec(v_val_3069_);
v___x_3071_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3070_, v___y_2995_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; uint8_t v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = lean_unbox(v_a_3072_);
lean_dec(v_a_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v_toGoalState_3075_; lean_object* v_mvarId_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3150_; 
v___x_3074_ = lean_st_ref_take(v___y_2994_);
v_toGoalState_3075_ = lean_ctor_get(v___x_3074_, 0);
v_mvarId_3076_ = lean_ctor_get(v___x_3074_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3078_ = v___x_3074_;
v_isShared_3079_ = v_isSharedCheck_3150_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_mvarId_3076_);
lean_inc(v_toGoalState_3075_);
lean_dec(v___x_3074_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3150_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_nextDeclIdx_3080_; lean_object* v_enodeMap_3081_; lean_object* v_exprs_3082_; lean_object* v_parents_3083_; lean_object* v_congrTable_3084_; lean_object* v_appMap_3085_; lean_object* v_indicesFound_3086_; lean_object* v_toProcess_3087_; uint8_t v_inconsistent_3088_; lean_object* v_nextIdx_3089_; lean_object* v_newRawFacts_3090_; lean_object* v_facts_3091_; lean_object* v_extThms_3092_; lean_object* v_ematch_3093_; lean_object* v_inj_3094_; lean_object* v_split_3095_; lean_object* v_clean_3096_; lean_object* v_sstates_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3149_; 
v_nextDeclIdx_3080_ = lean_ctor_get(v_toGoalState_3075_, 0);
v_enodeMap_3081_ = lean_ctor_get(v_toGoalState_3075_, 1);
v_exprs_3082_ = lean_ctor_get(v_toGoalState_3075_, 2);
v_parents_3083_ = lean_ctor_get(v_toGoalState_3075_, 3);
v_congrTable_3084_ = lean_ctor_get(v_toGoalState_3075_, 4);
v_appMap_3085_ = lean_ctor_get(v_toGoalState_3075_, 5);
v_indicesFound_3086_ = lean_ctor_get(v_toGoalState_3075_, 6);
v_toProcess_3087_ = lean_ctor_get(v_toGoalState_3075_, 7);
v_inconsistent_3088_ = lean_ctor_get_uint8(v_toGoalState_3075_, sizeof(void*)*17);
v_nextIdx_3089_ = lean_ctor_get(v_toGoalState_3075_, 8);
v_newRawFacts_3090_ = lean_ctor_get(v_toGoalState_3075_, 9);
v_facts_3091_ = lean_ctor_get(v_toGoalState_3075_, 10);
v_extThms_3092_ = lean_ctor_get(v_toGoalState_3075_, 11);
v_ematch_3093_ = lean_ctor_get(v_toGoalState_3075_, 12);
v_inj_3094_ = lean_ctor_get(v_toGoalState_3075_, 13);
v_split_3095_ = lean_ctor_get(v_toGoalState_3075_, 14);
v_clean_3096_ = lean_ctor_get(v_toGoalState_3075_, 15);
v_sstates_3097_ = lean_ctor_get(v_toGoalState_3075_, 16);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_toGoalState_3075_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3099_ = v_toGoalState_3075_;
v_isShared_3100_ = v_isSharedCheck_3149_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_sstates_3097_);
lean_inc(v_clean_3096_);
lean_inc(v_split_3095_);
lean_inc(v_inj_3094_);
lean_inc(v_ematch_3093_);
lean_inc(v_extThms_3092_);
lean_inc(v_facts_3091_);
lean_inc(v_newRawFacts_3090_);
lean_inc(v_nextIdx_3089_);
lean_inc(v_toProcess_3087_);
lean_inc(v_indicesFound_3086_);
lean_inc(v_appMap_3085_);
lean_inc(v_congrTable_3084_);
lean_inc(v_parents_3083_);
lean_inc(v_exprs_3082_);
lean_inc(v_enodeMap_3081_);
lean_inc(v_nextDeclIdx_3080_);
lean_dec(v_toGoalState_3075_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3149_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_box(0);
lean_inc_ref(v_self_3012_);
v___x_3102_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3081_, v_congrTable_3084_, v_self_3012_, v___x_3101_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 4, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_nextDeclIdx_3080_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_enodeMap_3081_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_exprs_3082_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_parents_3083_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3148_, 5, v_appMap_3085_);
lean_ctor_set(v_reuseFailAlloc_3148_, 6, v_indicesFound_3086_);
lean_ctor_set(v_reuseFailAlloc_3148_, 7, v_toProcess_3087_);
lean_ctor_set(v_reuseFailAlloc_3148_, 8, v_nextIdx_3089_);
lean_ctor_set(v_reuseFailAlloc_3148_, 9, v_newRawFacts_3090_);
lean_ctor_set(v_reuseFailAlloc_3148_, 10, v_facts_3091_);
lean_ctor_set(v_reuseFailAlloc_3148_, 11, v_extThms_3092_);
lean_ctor_set(v_reuseFailAlloc_3148_, 12, v_ematch_3093_);
lean_ctor_set(v_reuseFailAlloc_3148_, 13, v_inj_3094_);
lean_ctor_set(v_reuseFailAlloc_3148_, 14, v_split_3095_);
lean_ctor_set(v_reuseFailAlloc_3148_, 15, v_clean_3096_);
lean_ctor_set(v_reuseFailAlloc_3148_, 16, v_sstates_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*17, v_inconsistent_3088_);
v___x_3104_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3106_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3104_);
v___x_3106_ = v___x_3078_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_mvarId_3076_);
v___x_3106_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = lean_st_ref_put(v___y_2994_, v___x_3106_);
lean_inc_ref(v_rootNew_2991_);
lean_inc_ref(v_next_3013_);
lean_inc_ref_n(v_self_3012_, 3);
v___x_3108_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3108_, 0, v_self_3012_);
lean_ctor_set(v___x_3108_, 1, v_next_3013_);
lean_ctor_set(v___x_3108_, 2, v_rootNew_2991_);
lean_ctor_set(v___x_3108_, 3, v_self_3012_);
lean_ctor_set(v___x_3108_, 4, v_target_x3f_3015_);
lean_ctor_set(v___x_3108_, 5, v_proof_x3f_3016_);
lean_ctor_set(v___x_3108_, 6, v_size_3018_);
lean_ctor_set(v___x_3108_, 7, v_idx_3023_);
lean_ctor_set(v___x_3108_, 8, v_generation_3024_);
lean_ctor_set(v___x_3108_, 9, v_mt_3025_);
lean_ctor_set(v___x_3108_, 10, v_sTerms_3026_);
lean_ctor_set(v___x_3108_, 11, v_ematchDiagSource_3028_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12, v_flipped_3017_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12 + 1, v_interpreted_3019_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12 + 2, v_ctor_3020_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12 + 3, v_hasLambdas_3021_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12 + 4, v_heqProofs_3022_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*12 + 5, v_funCC_3027_);
v___x_3109_ = l_Lean_Meta_Grind_setENode___redArg(v_self_3012_, v___x_3108_, v___y_2994_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec_ref_known(v___x_3109_, 1);
v___x_3110_ = lean_st_ref_get(v___y_2994_);
lean_inc(v_fst_3070_);
v___x_3111_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3110_, v_fst_3070_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___x_3110_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v_self_3113_; lean_object* v_next_3114_; lean_object* v_root_3115_; lean_object* v_target_x3f_3116_; lean_object* v_proof_x3f_3117_; uint8_t v_flipped_3118_; lean_object* v_size_3119_; uint8_t v_interpreted_3120_; uint8_t v_ctor_3121_; uint8_t v_hasLambdas_3122_; uint8_t v_heqProofs_3123_; lean_object* v_idx_3124_; lean_object* v_generation_3125_; lean_object* v_mt_3126_; lean_object* v_sTerms_3127_; uint8_t v_funCC_3128_; lean_object* v_ematchDiagSource_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3137_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v_self_3113_ = lean_ctor_get(v_a_3112_, 0);
v_next_3114_ = lean_ctor_get(v_a_3112_, 1);
v_root_3115_ = lean_ctor_get(v_a_3112_, 2);
v_target_x3f_3116_ = lean_ctor_get(v_a_3112_, 4);
v_proof_x3f_3117_ = lean_ctor_get(v_a_3112_, 5);
v_flipped_3118_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12);
v_size_3119_ = lean_ctor_get(v_a_3112_, 6);
v_interpreted_3120_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12 + 1);
v_ctor_3121_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12 + 2);
v_hasLambdas_3122_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12 + 3);
v_heqProofs_3123_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12 + 4);
v_idx_3124_ = lean_ctor_get(v_a_3112_, 7);
v_generation_3125_ = lean_ctor_get(v_a_3112_, 8);
v_mt_3126_ = lean_ctor_get(v_a_3112_, 9);
v_sTerms_3127_ = lean_ctor_get(v_a_3112_, 10);
v_funCC_3128_ = lean_ctor_get_uint8(v_a_3112_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3129_ = lean_ctor_get(v_a_3112_, 11);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v_a_3112_, 3);
lean_dec(v_unused_3138_);
v___x_3131_ = v_a_3112_;
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_ematchDiagSource_3129_);
lean_inc(v_sTerms_3127_);
lean_inc(v_mt_3126_);
lean_inc(v_generation_3125_);
lean_inc(v_idx_3124_);
lean_inc(v_size_3119_);
lean_inc(v_proof_x3f_3117_);
lean_inc(v_target_x3f_3116_);
lean_inc(v_root_3115_);
lean_inc(v_next_3114_);
lean_inc(v_self_3113_);
lean_dec(v_a_3112_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3137_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 3, v_self_3012_);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_self_3113_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_next_3114_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_root_3115_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_self_3012_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_target_x3f_3116_);
lean_ctor_set(v_reuseFailAlloc_3136_, 5, v_proof_x3f_3117_);
lean_ctor_set(v_reuseFailAlloc_3136_, 6, v_size_3119_);
lean_ctor_set(v_reuseFailAlloc_3136_, 7, v_idx_3124_);
lean_ctor_set(v_reuseFailAlloc_3136_, 8, v_generation_3125_);
lean_ctor_set(v_reuseFailAlloc_3136_, 9, v_mt_3126_);
lean_ctor_set(v_reuseFailAlloc_3136_, 10, v_sTerms_3127_);
lean_ctor_set(v_reuseFailAlloc_3136_, 11, v_ematchDiagSource_3129_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12, v_flipped_3118_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12 + 1, v_interpreted_3120_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12 + 2, v_ctor_3121_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12 + 3, v_hasLambdas_3122_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12 + 4, v_heqProofs_3123_);
lean_ctor_set_uint8(v_reuseFailAlloc_3136_, sizeof(void*)*12 + 5, v_funCC_3128_);
v___x_3134_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3070_, v___x_3134_, v___y_2994_);
v___y_3048_ = v___x_3135_;
goto v___jp_3047_;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_fst_3070_);
lean_dec_ref(v_next_3013_);
lean_dec_ref(v_self_3012_);
lean_del_object(v___x_3010_);
lean_del_object(v___x_3003_);
lean_dec(v_snd_3001_);
lean_dec_ref(v_rootNew_2991_);
v_a_3139_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3111_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3111_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_dec(v_fst_3070_);
lean_dec_ref(v_self_3012_);
v___y_3048_ = v___x_3109_;
goto v___jp_3047_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3070_);
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
goto v___jp_3032_;
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec(v_fst_3070_);
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_next_3013_);
lean_dec_ref(v_self_3012_);
lean_del_object(v___x_3010_);
lean_del_object(v___x_3003_);
lean_dec(v_snd_3001_);
lean_dec_ref(v_rootNew_2991_);
v_a_3151_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3071_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3071_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
goto v___jp_3032_;
}
}
}
}
else
{
lean_dec_ref(v___x_3058_);
lean_dec(v_ematchDiagSource_3028_);
lean_dec(v_sTerms_3026_);
lean_dec(v_mt_3025_);
lean_dec(v_generation_3024_);
lean_dec(v_idx_3023_);
lean_dec(v_size_3018_);
lean_dec(v_proof_x3f_3016_);
lean_dec(v_target_x3f_3015_);
lean_dec_ref(v_self_3012_);
v___y_3048_ = v___x_3059_;
goto v___jp_3047_;
}
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_3003_);
lean_dec(v_snd_3001_);
lean_dec_ref(v_rootNew_2991_);
v_a_3163_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3007_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3007_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
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
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2990_ = stack[0].m_obj;
lean_object* v_rootNew_2991_ = stack[1].m_obj;
uint8_t v_a_2992_ = stack[2].m_num;
lean_object* v_a_2993_ = stack[3].m_obj;
lean_object* v___y_2994_ = stack[4].m_obj;
lean_object* v___y_2995_ = stack[5].m_obj;
lean_object* v___y_2996_ = stack[6].m_obj;
lean_object* v___y_2997_ = stack[7].m_obj;
lean_object* v___y_2998_ = stack[8].m_obj;
lean_object* v___y_2999_ = stack[9].m_obj;
lean_object* v_res_3173_;
v_res_3173_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_2990_, v_rootNew_2991_, v_a_2992_, v_a_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
stack->m_obj
 = v_res_3173_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3174_, lean_object* v_rootNew_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v_a_26477__boxed_3185_; lean_object* v_res_3186_; 
v_a_26477__boxed_3185_ = lean_unbox(v_a_3176_);
v_res_3186_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3174_, v_rootNew_3175_, v_a_26477__boxed_3185_, v_a_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v_lhs_3174_);
return v_res_3186_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3187_, lean_object* v_rootNew_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3188_, v_a_3193_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = lean_box(0);
lean_inc_ref(v_lhs_3187_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v_lhs_3187_);
v___x_3204_ = lean_unbox(v_a_3201_);
lean_dec(v_a_3201_);
v___x_3205_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3187_, v_rootNew_3188_, v___x_3204_, v___x_3203_, v_a_3189_, v_a_3193_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec_ref(v_lhs_3187_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3219_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3219_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3219_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_fst_3210_; 
v_fst_3210_ = lean_ctor_get(v_a_3206_, 0);
lean_inc(v_fst_3210_);
lean_dec(v_a_3206_);
if (lean_obj_tag(v_fst_3210_) == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3211_);
v___x_3213_ = v___x_3208_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
else
{
lean_object* v_val_3215_; lean_object* v___x_3217_; 
v_val_3215_ = lean_ctor_get(v_fst_3210_, 0);
lean_inc(v_val_3215_);
lean_dec_ref_known(v_fst_3210_, 1);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v_val_3215_);
v___x_3217_ = v___x_3208_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_val_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
v_a_3220_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3205_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3205_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_rootNew_3188_);
lean_dec_ref(v_lhs_3187_);
v_a_3228_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3200_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3200_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_3187_ = stack[0].m_obj;
lean_object* v_rootNew_3188_ = stack[1].m_obj;
lean_object* v_a_3189_ = stack[2].m_obj;
lean_object* v_a_3190_ = stack[3].m_obj;
lean_object* v_a_3191_ = stack[4].m_obj;
lean_object* v_a_3192_ = stack[5].m_obj;
lean_object* v_a_3193_ = stack[6].m_obj;
lean_object* v_a_3194_ = stack[7].m_obj;
lean_object* v_a_3195_ = stack[8].m_obj;
lean_object* v_a_3196_ = stack[9].m_obj;
lean_object* v_a_3197_ = stack[10].m_obj;
lean_object* v_a_3198_ = stack[11].m_obj;
lean_object* v_res_3236_;
v_res_3236_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3187_, v_rootNew_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
stack->m_obj
 = v_res_3236_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3237_, lean_object* v_rootNew_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3237_, v_rootNew_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec(v_a_3239_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3251_, lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3251_, v_x_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3256_, lean_object* v_00_u03b2_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3256_, v_00_u03b2_3257_, v_x_3258_, v_x_3259_);
lean_dec_ref(v_x_3258_);
lean_dec_ref(v___x_3256_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3261_, v_x_3263_, v_x_3264_, v_x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3267_, lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3267_, v_00_u03b2_3268_, v_x_3269_, v_x_3270_, v_x_3271_);
lean_dec_ref(v___x_3267_);
return v_res_3272_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3273_, lean_object* v_rootNew_3274_, uint8_t v_a_3275_, lean_object* v_inst_3276_, lean_object* v_a_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3273_, v_rootNew_3274_, v_a_3275_, v_a_3277_, v___y_3278_, v___y_3282_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_3273_ = stack[0].m_obj;
lean_object* v_rootNew_3274_ = stack[1].m_obj;
uint8_t v_a_3275_ = stack[2].m_num;
lean_object* v_a_3277_ = stack[4].m_obj;
lean_object* v___y_3278_ = stack[5].m_obj;
lean_object* v___y_3279_ = stack[6].m_obj;
lean_object* v___y_3280_ = stack[7].m_obj;
lean_object* v___y_3281_ = stack[8].m_obj;
lean_object* v___y_3282_ = stack[9].m_obj;
lean_object* v___y_3283_ = stack[10].m_obj;
lean_object* v___y_3284_ = stack[11].m_obj;
lean_object* v___y_3285_ = stack[12].m_obj;
lean_object* v___y_3286_ = stack[13].m_obj;
lean_object* v___y_3287_ = stack[14].m_obj;
lean_object* v_res_3290_;
v_res_3290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3273_, v_rootNew_3274_, v_a_3275_, lean_box(0), v_a_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
stack->m_obj
 = v_res_3290_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3291_, lean_object* v_rootNew_3292_, lean_object* v_a_3293_, lean_object* v_inst_3294_, lean_object* v_a_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
uint8_t v_a_27023__boxed_3307_; lean_object* v_res_3308_; 
v_a_27023__boxed_3307_ = lean_unbox(v_a_3293_);
v_res_3308_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3291_, v_rootNew_3292_, v_a_27023__boxed_3307_, v_inst_3294_, v_a_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v_lhs_3291_);
return v_res_3308_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3309_, lean_object* v_00_u03b2_3310_, lean_object* v_x_3311_, size_t v_x_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v___x_3314_; 
lean_inc_ref(v_x_3311_);
v___x_3314_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3309_, v_x_3311_, v_x_3312_, v_x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3309_ = stack[0].m_obj;
lean_object* v_x_3311_ = stack[2].m_obj;
size_t v_x_3312_ = stack[3].m_num;
lean_object* v_x_3313_ = stack[4].m_obj;
lean_object* v_res_3315_;
v_res_3315_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3309_, lean_box(0), v_x_3311_, v_x_3312_, v_x_3313_);
stack->m_obj
 = v_res_3315_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3316_, lean_object* v_00_u03b2_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
size_t v_x_27093__boxed_3321_; lean_object* v_res_3322_; 
v_x_27093__boxed_3321_ = lean_unbox_usize(v_x_3319_);
lean_dec(v_x_3319_);
v_res_3322_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3316_, v_00_u03b2_3317_, v_x_3318_, v_x_27093__boxed_3321_, v_x_3320_);
lean_dec_ref(v_x_3318_);
lean_dec_ref(v___x_3316_);
return v_res_3322_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3323_, lean_object* v_00_u03b2_3324_, lean_object* v_x_3325_, size_t v_x_3326_, size_t v_x_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3323_, v_x_3325_, v_x_3326_, v_x_3327_, v_x_3328_, v_x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3323_ = stack[0].m_obj;
lean_object* v_x_3325_ = stack[2].m_obj;
size_t v_x_3326_ = stack[3].m_num;
size_t v_x_3327_ = stack[4].m_num;
lean_object* v_x_3328_ = stack[5].m_obj;
lean_object* v_x_3329_ = stack[6].m_obj;
lean_object* v_res_3331_;
v_res_3331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3323_, lean_box(0), v_x_3325_, v_x_3326_, v_x_3327_, v_x_3328_, v_x_3329_);
stack->m_obj
 = v_res_3331_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3332_, lean_object* v_00_u03b2_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
size_t v_x_27116__boxed_3339_; size_t v_x_27117__boxed_3340_; lean_object* v_res_3341_; 
v_x_27116__boxed_3339_ = lean_unbox_usize(v_x_3335_);
lean_dec(v_x_3335_);
v_x_27117__boxed_3340_ = lean_unbox_usize(v_x_3336_);
lean_dec(v_x_3336_);
v_res_3341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3332_, v_00_u03b2_3333_, v_x_3334_, v_x_27116__boxed_3339_, v_x_27117__boxed_3340_, v_x_3337_, v_x_3338_);
lean_dec_ref(v___x_3332_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3342_, lean_object* v_00_u03b2_3343_, lean_object* v_keys_3344_, lean_object* v_vals_3345_, lean_object* v_heq_3346_, lean_object* v_i_3347_, lean_object* v_k_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3342_, v_keys_3344_, v_vals_3345_, v_i_3347_, v_k_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3350_, lean_object* v_00_u03b2_3351_, lean_object* v_keys_3352_, lean_object* v_vals_3353_, lean_object* v_heq_3354_, lean_object* v_i_3355_, lean_object* v_k_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3350_, v_00_u03b2_3351_, v_keys_3352_, v_vals_3353_, v_heq_3354_, v_i_3355_, v_k_3356_);
lean_dec_ref(v_vals_3353_);
lean_dec_ref(v_keys_3352_);
lean_dec_ref(v___x_3350_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3358_, lean_object* v_00_u03b2_3359_, lean_object* v_n_3360_, lean_object* v_k_3361_, lean_object* v_v_3362_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3358_, v_n_3360_, v_k_3361_, v_v_3362_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3364_, lean_object* v_00_u03b2_3365_, lean_object* v_n_3366_, lean_object* v_k_3367_, lean_object* v_v_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3364_, v_00_u03b2_3365_, v_n_3366_, v_k_3367_, v_v_3368_);
lean_dec_ref(v___x_3364_);
return v_res_3369_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3370_, lean_object* v_00_u03b2_3371_, size_t v_depth_3372_, lean_object* v_keys_3373_, lean_object* v_vals_3374_, lean_object* v_heq_3375_, lean_object* v_i_3376_, lean_object* v_entries_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3370_, v_depth_3372_, v_keys_3373_, v_vals_3374_, v_i_3376_, v_entries_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3370_ = stack[0].m_obj;
size_t v_depth_3372_ = stack[2].m_num;
lean_object* v_keys_3373_ = stack[3].m_obj;
lean_object* v_vals_3374_ = stack[4].m_obj;
lean_object* v_i_3376_ = stack[6].m_obj;
lean_object* v_entries_3377_ = stack[7].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3370_, lean_box(0), v_depth_3372_, v_keys_3373_, v_vals_3374_, lean_box(0), v_i_3376_, v_entries_3377_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3380_, lean_object* v_00_u03b2_3381_, lean_object* v_depth_3382_, lean_object* v_keys_3383_, lean_object* v_vals_3384_, lean_object* v_heq_3385_, lean_object* v_i_3386_, lean_object* v_entries_3387_){
_start:
{
size_t v_depth_boxed_3388_; lean_object* v_res_3389_; 
v_depth_boxed_3388_ = lean_unbox_usize(v_depth_3382_);
lean_dec(v_depth_3382_);
v_res_3389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3380_, v_00_u03b2_3381_, v_depth_boxed_3388_, v_keys_3383_, v_vals_3384_, v_heq_3385_, v_i_3386_, v_entries_3387_);
lean_dec_ref(v_vals_3384_);
lean_dec_ref(v_keys_3383_);
lean_dec_ref(v___x_3380_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3390_, lean_object* v_00_u03b2_3391_, lean_object* v_x_3392_, lean_object* v_x_3393_, lean_object* v_x_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3390_, v_x_3392_, v_x_3393_, v_x_3394_, v_x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3397_, lean_object* v_00_u03b2_3398_, lean_object* v_x_3399_, lean_object* v_x_3400_, lean_object* v_x_3401_, lean_object* v_x_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3397_, v_00_u03b2_3398_, v_x_3399_, v_x_3400_, v_x_3401_, v_x_3402_);
lean_dec_ref(v___x_3397_);
return v_res_3403_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
if (lean_obj_tag(v_as_x27_3404_) == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_b_3405_);
return v___x_3417_;
}
else
{
lean_object* v_head_3418_; lean_object* v_tail_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_head_3418_ = lean_ctor_get(v_as_x27_3404_, 0);
v_tail_3419_ = lean_ctor_get(v_as_x27_3404_, 1);
v___x_3420_ = lean_box(0);
lean_inc(v_head_3418_);
v___x_3421_ = l_Lean_Meta_Grind_propagateUp(v_head_3418_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_dec_ref_known(v___x_3421_, 1);
v_as_x27_3404_ = v_tail_3419_;
v_b_3405_ = v___x_3420_;
goto _start;
}
else
{
return v___x_3421_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3404_ = stack[0].m_obj;
lean_object* v_b_3405_ = stack[1].m_obj;
lean_object* v___y_3406_ = stack[2].m_obj;
lean_object* v___y_3407_ = stack[3].m_obj;
lean_object* v___y_3408_ = stack[4].m_obj;
lean_object* v___y_3409_ = stack[5].m_obj;
lean_object* v___y_3410_ = stack[6].m_obj;
lean_object* v___y_3411_ = stack[7].m_obj;
lean_object* v___y_3412_ = stack[8].m_obj;
lean_object* v___y_3413_ = stack[9].m_obj;
lean_object* v___y_3414_ = stack[10].m_obj;
lean_object* v___y_3415_ = stack[11].m_obj;
lean_object* v_res_3423_;
v_res_3423_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3404_, v_b_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
stack->m_obj
 = v_res_3423_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3424_, lean_object* v_b_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3424_, v_b_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v_as_x27_3424_);
return v_res_3437_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3438_, lean_object* v_b_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
if (lean_obj_tag(v_as_x27_3438_) == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_b_3439_);
return v___x_3451_;
}
else
{
lean_object* v_head_3452_; lean_object* v_tail_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_head_3452_ = lean_ctor_get(v_as_x27_3438_, 0);
v_tail_3453_ = lean_ctor_get(v_as_x27_3438_, 1);
v___x_3454_ = lean_box(0);
lean_inc(v_head_3452_);
v___x_3455_ = l_Lean_Meta_Grind_propagateDown(v_head_3452_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
v_as_x27_3438_ = v_tail_3453_;
v_b_3439_ = v___x_3454_;
goto _start;
}
else
{
return v___x_3455_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3438_ = stack[0].m_obj;
lean_object* v_b_3439_ = stack[1].m_obj;
lean_object* v___y_3440_ = stack[2].m_obj;
lean_object* v___y_3441_ = stack[3].m_obj;
lean_object* v___y_3442_ = stack[4].m_obj;
lean_object* v___y_3443_ = stack[5].m_obj;
lean_object* v___y_3444_ = stack[6].m_obj;
lean_object* v___y_3445_ = stack[7].m_obj;
lean_object* v___y_3446_ = stack[8].m_obj;
lean_object* v___y_3447_ = stack[9].m_obj;
lean_object* v___y_3448_ = stack[10].m_obj;
lean_object* v___y_3449_ = stack[11].m_obj;
lean_object* v_res_3457_;
v_res_3457_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3438_, v_b_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
stack->m_obj
 = v_res_3457_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3458_, lean_object* v_b_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3458_, v_b_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec(v_as_x27_3458_);
return v_res_3471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_cls_3475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3476_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3477_ = l_Lean_Name_append(v___x_3476_, v_cls_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3480_ = l_Lean_stringToMessageData(v___x_3479_);
return v___x_3480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3483_ = l_Lean_stringToMessageData(v___x_3482_);
return v___x_3483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3486_ = l_Lean_stringToMessageData(v___x_3485_);
return v___x_3486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3489_ = l_Lean_stringToMessageData(v___x_3488_);
return v___x_3489_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3490_, uint8_t v_isHEq_3491_, lean_object* v_lhs_3492_, lean_object* v_rhs_3493_, lean_object* v_lhsNode_3494_, lean_object* v_rhsNode_3495_, lean_object* v_lhsRoot_3496_, lean_object* v_rhsRoot_3497_, uint8_t v_flipped_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3563_; lean_object* v___y_3564_; uint8_t v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; lean_object* v___y_3628_; uint8_t v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; uint8_t v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; uint8_t v___y_3657_; uint8_t v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3663_; uint8_t v___y_3664_; uint8_t v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; uint8_t v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_toCold_3748_; lean_object* v_options_3749_; lean_object* v_inheritedTraceOptions_3750_; uint8_t v_hasTrace_3751_; lean_object* v_cls_3752_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v_fns_u2082_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v_fns_u2081_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; 
v_toCold_3748_ = lean_ctor_get(v_a_3507_, 0);
v_options_3749_ = lean_ctor_get(v_toCold_3748_, 2);
v_inheritedTraceOptions_3750_ = lean_ctor_get(v_toCold_3748_, 11);
v_hasTrace_3751_ = lean_ctor_get_uint8(v_options_3749_, sizeof(void*)*1);
v_cls_3752_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3751_ == 0)
{
v___y_3872_ = v_a_3499_;
v___y_3873_ = v_a_3500_;
v___y_3874_ = v_a_3501_;
v___y_3875_ = v_a_3502_;
v___y_3876_ = v_a_3503_;
v___y_3877_ = v_a_3504_;
v___y_3878_ = v_a_3505_;
v___y_3879_ = v_a_3506_;
v___y_3880_ = v_a_3507_;
v___y_3881_ = v_a_3508_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3750_, v_options_3749_, v___x_3952_);
if (v___x_3953_ == 0)
{
v___y_3872_ = v_a_3499_;
v___y_3873_ = v_a_3500_;
v___y_3874_ = v_a_3501_;
v___y_3875_ = v_a_3502_;
v___y_3876_ = v_a_3503_;
v___y_3877_ = v_a_3504_;
v___y_3878_ = v_a_3505_;
v___y_3879_ = v_a_3506_;
v___y_3880_ = v_a_3507_;
v___y_3881_ = v_a_3508_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Lean_Meta_Grind_updateLastTag(v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v___x_3955_; 
lean_dec_ref_known(v___x_3954_, 1);
lean_inc_ref(v_lhs_3492_);
v___x_3955_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3492_, v_a_3499_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
lean_inc_ref(v_rhs_3493_);
v___x_3957_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3493_, v_a_3499_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v_a_3956_);
v___x_3961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3960_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v_a_3958_);
v___x_3964_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3752_, v___x_3963_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_dec_ref_known(v___x_3964_, 1);
v___y_3872_ = v_a_3499_;
v___y_3873_ = v_a_3500_;
v___y_3874_ = v_a_3501_;
v___y_3875_ = v_a_3502_;
v___y_3876_ = v_a_3503_;
v___y_3877_ = v_a_3504_;
v___y_3878_ = v_a_3505_;
v___y_3879_ = v_a_3506_;
v___y_3880_ = v_a_3507_;
v___y_3881_ = v_a_3508_;
goto v___jp_3871_;
}
else
{
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhsNode_3494_);
lean_dec_ref(v_rhs_3493_);
lean_dec_ref(v_lhs_3492_);
lean_dec_ref(v_proof_3490_);
return v___x_3964_;
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_a_3956_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhsNode_3494_);
lean_dec_ref(v_rhs_3493_);
lean_dec_ref(v_lhs_3492_);
lean_dec_ref(v_proof_3490_);
v_a_3965_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3957_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3957_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhsNode_3494_);
lean_dec_ref(v_rhs_3493_);
lean_dec_ref(v_lhs_3492_);
lean_dec_ref(v_proof_3490_);
v_a_3973_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3955_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3955_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhsNode_3494_);
lean_dec_ref(v_rhs_3493_);
lean_dec_ref(v_lhs_3492_);
lean_dec_ref(v_proof_3490_);
return v___x_3954_;
}
}
}
v___jp_3510_:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3517_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3553_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3553_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3553_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
uint8_t v___x_3532_; 
v___x_3532_ = lean_unbox(v_a_3528_);
lean_dec(v_a_3528_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_del_object(v___x_3530_);
v___x_3533_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3516_);
lean_dec(v___y_3516_);
v___x_3534_ = lean_box(0);
v___x_3535_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3533_, v___x_3534_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___x_3533_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3536_; 
lean_dec_ref_known(v___x_3535_, 1);
v___x_3536_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3514_, v___x_3534_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v___x_3537_; 
lean_dec_ref_known(v___x_3536_, 1);
v___x_3537_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3513_, v___y_3511_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3513_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3537_, 1);
v___x_3538_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3512_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3547_; 
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v___x_3538_, 0);
lean_dec(v_unused_3548_);
v___x_3540_ = v___x_3538_;
v_isShared_3541_ = v_isSharedCheck_3547_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v___x_3538_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3547_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
uint8_t v___x_3542_; 
v___x_3542_ = l_Lean_Expr_isTrue(v___y_3515_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3544_; 
lean_dec(v___y_3514_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v___x_3534_);
v___x_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3534_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
else
{
lean_object* v___x_3546_; 
lean_del_object(v___x_3540_);
v___x_3546_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3514_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3514_);
return v___x_3546_;
}
}
}
else
{
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
return v___x_3538_;
}
}
else
{
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v___y_3512_);
return v___x_3537_;
}
}
else
{
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v___x_3536_;
}
}
else
{
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v___x_3535_;
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
v___x_3549_ = lean_box(0);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3549_);
v___x_3551_ = v___x_3530_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
v_a_3554_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3527_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3527_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
v___jp_3562_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_inc_ref(v___y_3569_);
v___x_3599_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3599_, 0, v___y_3569_);
lean_ctor_set(v___x_3599_, 1, v___y_3583_);
lean_ctor_set(v___x_3599_, 2, v___y_3563_);
lean_ctor_set(v___x_3599_, 3, v___y_3579_);
lean_ctor_set(v___x_3599_, 4, v___y_3590_);
lean_ctor_set(v___x_3599_, 5, v___y_3584_);
lean_ctor_set(v___x_3599_, 6, v___y_3576_);
lean_ctor_set(v___x_3599_, 7, v___y_3595_);
lean_ctor_set(v___x_3599_, 8, v___y_3564_);
lean_ctor_set(v___x_3599_, 9, v___y_3566_);
lean_ctor_set(v___x_3599_, 10, v___y_3567_);
lean_ctor_set(v___x_3599_, 11, v___y_3568_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12, v___y_3575_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12 + 1, v___y_3594_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12 + 2, v___y_3565_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12 + 3, v___y_3589_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12 + 4, v___y_3598_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*12 + 5, v___y_3591_);
lean_inc_ref(v___y_3592_);
v___x_3600_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3592_, v___x_3599_, v___y_3596_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v___x_3601_; 
lean_dec_ref_known(v___x_3600_, 1);
lean_inc_ref(v___y_3580_);
v___x_3601_ = l_Lean_Meta_Grind_propagateBeta(v___y_3580_, v___y_3578_, v___y_3596_, v___y_3574_, v___y_3585_, v___y_3597_, v___y_3572_, v___y_3571_, v___y_3570_, v___y_3588_, v___y_3593_, v___y_3577_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref_known(v___x_3601_, 1);
lean_inc_ref(v___y_3586_);
v___x_3602_ = l_Lean_Meta_Grind_propagateBeta(v___y_3586_, v___y_3582_, v___y_3596_, v___y_3574_, v___y_3585_, v___y_3597_, v___y_3572_, v___y_3571_, v___y_3570_, v___y_3588_, v___y_3593_, v___y_3577_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3603_; 
lean_dec_ref_known(v___x_3602_, 1);
v___x_3603_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3497_, v_lhsRoot_3496_, v___y_3596_, v___y_3570_, v___y_3588_, v___y_3593_, v___y_3577_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3581_, v___y_3596_);
lean_dec_ref(v___y_3581_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3606_; 
lean_dec_ref_known(v___x_3605_, 1);
lean_inc_ref(v___y_3592_);
v___x_3606_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3573_, v___y_3592_, v___y_3596_, v___y_3574_, v___y_3585_, v___y_3597_, v___y_3572_, v___y_3571_, v___y_3570_, v___y_3588_, v___y_3593_, v___y_3577_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v___x_3607_; 
lean_dec_ref_known(v___x_3606_, 1);
v___x_3607_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3596_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; uint8_t v___x_3609_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = lean_unbox(v_a_3608_);
lean_dec(v_a_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
v___x_3610_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3569_, v___y_3596_, v___y_3574_, v___y_3585_, v___y_3597_, v___y_3572_, v___y_3571_, v___y_3570_, v___y_3588_, v___y_3593_, v___y_3577_);
lean_dec_ref(v___y_3569_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref_known(v___x_3610_, 1);
v___y_3511_ = v___y_3586_;
v___y_3512_ = v_a_3604_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3587_;
v___y_3515_ = v___y_3592_;
v___y_3516_ = v___y_3573_;
v___y_3517_ = v___y_3596_;
v___y_3518_ = v___y_3574_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3597_;
v___y_3521_ = v___y_3572_;
v___y_3522_ = v___y_3571_;
v___y_3523_ = v___y_3570_;
v___y_3524_ = v___y_3588_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3577_;
goto v___jp_3510_;
}
else
{
lean_dec(v_a_3604_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
return v___x_3610_;
}
}
else
{
lean_dec_ref(v___y_3569_);
v___y_3511_ = v___y_3586_;
v___y_3512_ = v_a_3604_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3587_;
v___y_3515_ = v___y_3592_;
v___y_3516_ = v___y_3573_;
v___y_3517_ = v___y_3596_;
v___y_3518_ = v___y_3574_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3597_;
v___y_3521_ = v___y_3572_;
v___y_3522_ = v___y_3571_;
v___y_3523_ = v___y_3570_;
v___y_3524_ = v___y_3588_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3577_;
goto v___jp_3510_;
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_a_3604_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
v_a_3611_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3607_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_dec(v_a_3604_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
return v___x_3606_;
}
}
else
{
lean_dec(v_a_3604_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
return v___x_3605_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
v_a_3619_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3603_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3603_);
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
else
{
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
return v___x_3602_;
}
}
else
{
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
return v___x_3601_;
}
}
else
{
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
return v___x_3600_;
}
}
v___jp_3627_:
{
if (v_isHEq_3491_ == 0)
{
if (v___y_3663_ == 0)
{
v___y_3563_ = v___y_3628_;
v___y_3564_ = v___y_3630_;
v___y_3565_ = v___y_3629_;
v___y_3566_ = v___y_3633_;
v___y_3567_ = v___y_3632_;
v___y_3568_ = v___y_3631_;
v___y_3569_ = v___y_3634_;
v___y_3570_ = v___y_3635_;
v___y_3571_ = v___y_3636_;
v___y_3572_ = v___y_3637_;
v___y_3573_ = v___y_3639_;
v___y_3574_ = v___y_3640_;
v___y_3575_ = v___y_3641_;
v___y_3576_ = v___y_3642_;
v___y_3577_ = v___y_3643_;
v___y_3578_ = v___y_3644_;
v___y_3579_ = v___y_3645_;
v___y_3580_ = v___y_3646_;
v___y_3581_ = v___y_3647_;
v___y_3582_ = v___y_3648_;
v___y_3583_ = v___y_3649_;
v___y_3584_ = v___y_3650_;
v___y_3585_ = v___y_3651_;
v___y_3586_ = v___y_3652_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3653_;
v___y_3589_ = v___y_3664_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3656_;
v___y_3593_ = v___y_3659_;
v___y_3594_ = v___y_3658_;
v___y_3595_ = v___y_3660_;
v___y_3596_ = v___y_3661_;
v___y_3597_ = v___y_3662_;
v___y_3598_ = v___y_3638_;
goto v___jp_3562_;
}
else
{
v___y_3563_ = v___y_3628_;
v___y_3564_ = v___y_3630_;
v___y_3565_ = v___y_3629_;
v___y_3566_ = v___y_3633_;
v___y_3567_ = v___y_3632_;
v___y_3568_ = v___y_3631_;
v___y_3569_ = v___y_3634_;
v___y_3570_ = v___y_3635_;
v___y_3571_ = v___y_3636_;
v___y_3572_ = v___y_3637_;
v___y_3573_ = v___y_3639_;
v___y_3574_ = v___y_3640_;
v___y_3575_ = v___y_3641_;
v___y_3576_ = v___y_3642_;
v___y_3577_ = v___y_3643_;
v___y_3578_ = v___y_3644_;
v___y_3579_ = v___y_3645_;
v___y_3580_ = v___y_3646_;
v___y_3581_ = v___y_3647_;
v___y_3582_ = v___y_3648_;
v___y_3583_ = v___y_3649_;
v___y_3584_ = v___y_3650_;
v___y_3585_ = v___y_3651_;
v___y_3586_ = v___y_3652_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3653_;
v___y_3589_ = v___y_3664_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3656_;
v___y_3593_ = v___y_3659_;
v___y_3594_ = v___y_3658_;
v___y_3595_ = v___y_3660_;
v___y_3596_ = v___y_3661_;
v___y_3597_ = v___y_3662_;
v___y_3598_ = v___y_3663_;
goto v___jp_3562_;
}
}
else
{
v___y_3563_ = v___y_3628_;
v___y_3564_ = v___y_3630_;
v___y_3565_ = v___y_3629_;
v___y_3566_ = v___y_3633_;
v___y_3567_ = v___y_3632_;
v___y_3568_ = v___y_3631_;
v___y_3569_ = v___y_3634_;
v___y_3570_ = v___y_3635_;
v___y_3571_ = v___y_3636_;
v___y_3572_ = v___y_3637_;
v___y_3573_ = v___y_3639_;
v___y_3574_ = v___y_3640_;
v___y_3575_ = v___y_3641_;
v___y_3576_ = v___y_3642_;
v___y_3577_ = v___y_3643_;
v___y_3578_ = v___y_3644_;
v___y_3579_ = v___y_3645_;
v___y_3580_ = v___y_3646_;
v___y_3581_ = v___y_3647_;
v___y_3582_ = v___y_3648_;
v___y_3583_ = v___y_3649_;
v___y_3584_ = v___y_3650_;
v___y_3585_ = v___y_3651_;
v___y_3586_ = v___y_3652_;
v___y_3587_ = v___y_3654_;
v___y_3588_ = v___y_3653_;
v___y_3589_ = v___y_3664_;
v___y_3590_ = v___y_3655_;
v___y_3591_ = v___y_3657_;
v___y_3592_ = v___y_3656_;
v___y_3593_ = v___y_3659_;
v___y_3594_ = v___y_3658_;
v___y_3595_ = v___y_3660_;
v___y_3596_ = v___y_3661_;
v___y_3597_ = v___y_3662_;
v___y_3598_ = v_isHEq_3491_;
goto v___jp_3562_;
}
}
v___jp_3665_:
{
lean_object* v___x_3688_; 
v___x_3688_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3676_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3688_) == 0)
{
uint8_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_dec_ref_known(v___x_3688_, 1);
v___x_3689_ = 0;
v___x_3690_ = lean_st_ref_get(v___y_3678_);
v___x_3691_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3690_, v_lhs_3492_, v___x_3689_);
lean_dec(v___x_3690_);
v___x_3692_ = lean_st_ref_get(v___y_3678_);
lean_inc_ref(v___y_3672_);
v___x_3693_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3692_, v___y_3672_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___x_3692_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_self_3695_; lean_object* v_root_3696_; lean_object* v_congr_3697_; lean_object* v_target_x3f_3698_; lean_object* v_proof_x3f_3699_; uint8_t v_flipped_3700_; lean_object* v_size_3701_; uint8_t v_interpreted_3702_; uint8_t v_ctor_3703_; uint8_t v_hasLambdas_3704_; uint8_t v_heqProofs_3705_; lean_object* v_idx_3706_; lean_object* v_generation_3707_; lean_object* v_mt_3708_; lean_object* v_sTerms_3709_; uint8_t v_funCC_3710_; lean_object* v_ematchDiagSource_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3738_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_self_3695_ = lean_ctor_get(v_a_3694_, 0);
v_root_3696_ = lean_ctor_get(v_a_3694_, 2);
v_congr_3697_ = lean_ctor_get(v_a_3694_, 3);
v_target_x3f_3698_ = lean_ctor_get(v_a_3694_, 4);
v_proof_x3f_3699_ = lean_ctor_get(v_a_3694_, 5);
v_flipped_3700_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12);
v_size_3701_ = lean_ctor_get(v_a_3694_, 6);
v_interpreted_3702_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12 + 1);
v_ctor_3703_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12 + 2);
v_hasLambdas_3704_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12 + 3);
v_heqProofs_3705_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12 + 4);
v_idx_3706_ = lean_ctor_get(v_a_3694_, 7);
v_generation_3707_ = lean_ctor_get(v_a_3694_, 8);
v_mt_3708_ = lean_ctor_get(v_a_3694_, 9);
v_sTerms_3709_ = lean_ctor_get(v_a_3694_, 10);
v_funCC_3710_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3711_ = lean_ctor_get(v_a_3694_, 11);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; 
v_unused_3739_ = lean_ctor_get(v_a_3694_, 1);
lean_dec(v_unused_3739_);
v___x_3713_ = v_a_3694_;
v_isShared_3714_ = v_isSharedCheck_3738_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_ematchDiagSource_3711_);
lean_inc(v_sTerms_3709_);
lean_inc(v_mt_3708_);
lean_inc(v_generation_3707_);
lean_inc(v_idx_3706_);
lean_inc(v_size_3701_);
lean_inc(v_proof_x3f_3699_);
lean_inc(v_target_x3f_3698_);
lean_inc(v_congr_3697_);
lean_inc(v_root_3696_);
lean_inc(v_self_3695_);
lean_dec(v_a_3694_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3738_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_self_3715_; lean_object* v_next_3716_; lean_object* v_root_3717_; lean_object* v_congr_3718_; lean_object* v_target_x3f_3719_; lean_object* v_proof_x3f_3720_; uint8_t v_flipped_3721_; lean_object* v_size_3722_; uint8_t v_interpreted_3723_; uint8_t v_ctor_3724_; uint8_t v_hasLambdas_3725_; uint8_t v_heqProofs_3726_; lean_object* v_idx_3727_; lean_object* v_generation_3728_; lean_object* v_mt_3729_; lean_object* v_sTerms_3730_; uint8_t v_funCC_3731_; lean_object* v_ematchDiagSource_3732_; lean_object* v___x_3734_; 
v_self_3715_ = lean_ctor_get(v_rhsRoot_3497_, 0);
v_next_3716_ = lean_ctor_get(v_rhsRoot_3497_, 1);
v_root_3717_ = lean_ctor_get(v_rhsRoot_3497_, 2);
v_congr_3718_ = lean_ctor_get(v_rhsRoot_3497_, 3);
v_target_x3f_3719_ = lean_ctor_get(v_rhsRoot_3497_, 4);
v_proof_x3f_3720_ = lean_ctor_get(v_rhsRoot_3497_, 5);
v_flipped_3721_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12);
v_size_3722_ = lean_ctor_get(v_rhsRoot_3497_, 6);
v_interpreted_3723_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12 + 1);
v_ctor_3724_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12 + 2);
v_hasLambdas_3725_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12 + 3);
v_heqProofs_3726_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12 + 4);
v_idx_3727_ = lean_ctor_get(v_rhsRoot_3497_, 7);
v_generation_3728_ = lean_ctor_get(v_rhsRoot_3497_, 8);
v_mt_3729_ = lean_ctor_get(v_rhsRoot_3497_, 9);
v_sTerms_3730_ = lean_ctor_get(v_rhsRoot_3497_, 10);
v_funCC_3731_ = lean_ctor_get_uint8(v_rhsRoot_3497_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3732_ = lean_ctor_get(v_rhsRoot_3497_, 11);
lean_inc_ref(v_next_3716_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_next_3716_);
v___x_3734_ = v___x_3713_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_self_3695_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_next_3716_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_root_3696_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_congr_3697_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_target_x3f_3698_);
lean_ctor_set(v_reuseFailAlloc_3737_, 5, v_proof_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3737_, 6, v_size_3701_);
lean_ctor_set(v_reuseFailAlloc_3737_, 7, v_idx_3706_);
lean_ctor_set(v_reuseFailAlloc_3737_, 8, v_generation_3707_);
lean_ctor_set(v_reuseFailAlloc_3737_, 9, v_mt_3708_);
lean_ctor_set(v_reuseFailAlloc_3737_, 10, v_sTerms_3709_);
lean_ctor_set(v_reuseFailAlloc_3737_, 11, v_ematchDiagSource_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12, v_flipped_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12 + 1, v_interpreted_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12 + 2, v_ctor_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12 + 3, v_hasLambdas_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12 + 4, v_heqProofs_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, sizeof(void*)*12 + 5, v_funCC_3710_);
v___x_3734_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3675_, v___x_3734_, v___y_3678_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3736_; 
lean_dec_ref_known(v___x_3735_, 1);
v___x_3736_ = lean_nat_add(v_size_3722_, v___y_3670_);
lean_dec(v___y_3670_);
if (v_hasLambdas_3725_ == 0)
{
lean_inc(v_idx_3727_);
lean_inc(v_target_x3f_3719_);
lean_inc(v_proof_x3f_3720_);
lean_inc_ref(v_congr_3718_);
lean_inc_ref(v_self_3715_);
lean_inc(v_mt_3729_);
lean_inc(v_sTerms_3730_);
lean_inc(v_ematchDiagSource_3732_);
lean_inc(v_generation_3728_);
lean_inc_ref(v_root_3717_);
v___y_3628_ = v_root_3717_;
v___y_3629_ = v_ctor_3724_;
v___y_3630_ = v_generation_3728_;
v___y_3631_ = v_ematchDiagSource_3732_;
v___y_3632_ = v_sTerms_3730_;
v___y_3633_ = v_mt_3729_;
v___y_3634_ = v_self_3715_;
v___y_3635_ = v___y_3684_;
v___y_3636_ = v___y_3683_;
v___y_3637_ = v___y_3682_;
v___y_3638_ = v___y_3674_;
v___y_3639_ = v___y_3676_;
v___y_3640_ = v___y_3679_;
v___y_3641_ = v_flipped_3721_;
v___y_3642_ = v___x_3736_;
v___y_3643_ = v___y_3687_;
v___y_3644_ = v___y_3668_;
v___y_3645_ = v_congr_3718_;
v___y_3646_ = v___y_3669_;
v___y_3647_ = v___y_3672_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___y_3677_;
v___y_3650_ = v_proof_x3f_3720_;
v___y_3651_ = v___y_3680_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3685_;
v___y_3654_ = v___x_3691_;
v___y_3655_ = v_target_x3f_3719_;
v___y_3656_ = v___y_3673_;
v___y_3657_ = v_funCC_3731_;
v___y_3658_ = v_interpreted_3723_;
v___y_3659_ = v___y_3686_;
v___y_3660_ = v_idx_3727_;
v___y_3661_ = v___y_3678_;
v___y_3662_ = v___y_3681_;
v___y_3663_ = v_heqProofs_3726_;
v___y_3664_ = v___y_3666_;
goto v___jp_3627_;
}
else
{
lean_inc(v_idx_3727_);
lean_inc(v_target_x3f_3719_);
lean_inc(v_proof_x3f_3720_);
lean_inc_ref(v_congr_3718_);
lean_inc_ref(v_self_3715_);
lean_inc(v_mt_3729_);
lean_inc(v_sTerms_3730_);
lean_inc(v_ematchDiagSource_3732_);
lean_inc(v_generation_3728_);
lean_inc_ref(v_root_3717_);
v___y_3628_ = v_root_3717_;
v___y_3629_ = v_ctor_3724_;
v___y_3630_ = v_generation_3728_;
v___y_3631_ = v_ematchDiagSource_3732_;
v___y_3632_ = v_sTerms_3730_;
v___y_3633_ = v_mt_3729_;
v___y_3634_ = v_self_3715_;
v___y_3635_ = v___y_3684_;
v___y_3636_ = v___y_3683_;
v___y_3637_ = v___y_3682_;
v___y_3638_ = v___y_3674_;
v___y_3639_ = v___y_3676_;
v___y_3640_ = v___y_3679_;
v___y_3641_ = v_flipped_3721_;
v___y_3642_ = v___x_3736_;
v___y_3643_ = v___y_3687_;
v___y_3644_ = v___y_3668_;
v___y_3645_ = v_congr_3718_;
v___y_3646_ = v___y_3669_;
v___y_3647_ = v___y_3672_;
v___y_3648_ = v___y_3671_;
v___y_3649_ = v___y_3677_;
v___y_3650_ = v_proof_x3f_3720_;
v___y_3651_ = v___y_3680_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3685_;
v___y_3654_ = v___x_3691_;
v___y_3655_ = v_target_x3f_3719_;
v___y_3656_ = v___y_3673_;
v___y_3657_ = v_funCC_3731_;
v___y_3658_ = v_interpreted_3723_;
v___y_3659_ = v___y_3686_;
v___y_3660_ = v_idx_3727_;
v___y_3661_ = v___y_3678_;
v___y_3662_ = v___y_3681_;
v___y_3663_ = v_heqProofs_3726_;
v___y_3664_ = v_hasLambdas_3725_;
goto v___jp_3627_;
}
}
else
{
lean_dec(v___x_3691_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
return v___x_3735_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v___x_3691_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
v_a_3740_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3693_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3693_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
return v___x_3688_;
}
}
v___jp_3753_:
{
lean_object* v_self_3769_; lean_object* v_next_3770_; lean_object* v_size_3771_; uint8_t v_hasLambdas_3772_; uint8_t v_heqProofs_3773_; lean_object* v___x_3774_; 
v_self_3769_ = lean_ctor_get(v_lhsRoot_3496_, 0);
v_next_3770_ = lean_ctor_get(v_lhsRoot_3496_, 1);
v_size_3771_ = lean_ctor_get(v_lhsRoot_3496_, 6);
v_hasLambdas_3772_ = lean_ctor_get_uint8(v_lhsRoot_3496_, sizeof(void*)*12 + 3);
v_heqProofs_3773_ = lean_ctor_get_uint8(v_lhsRoot_3496_, sizeof(void*)*12 + 4);
v___x_3774_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3769_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v_root_3776_; lean_object* v___x_3777_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___x_3774_, 1);
v_root_3776_ = lean_ctor_get(v_rhsNode_3495_, 2);
lean_inc_ref_n(v_root_3776_, 2);
lean_dec_ref(v_rhsNode_3495_);
lean_inc_ref(v_lhs_3492_);
v___x_3777_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3492_, v_root_3776_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_toCold_3778_; lean_object* v_options_3779_; uint8_t v_hasTrace_3780_; 
lean_dec_ref_known(v___x_3777_, 1);
v_toCold_3778_ = lean_ctor_get(v___y_3767_, 0);
v_options_3779_ = lean_ctor_get(v_toCold_3778_, 2);
v_hasTrace_3780_ = lean_ctor_get_uint8(v_options_3779_, sizeof(void*)*1);
if (v_hasTrace_3780_ == 0)
{
lean_inc_ref(v_next_3770_);
lean_inc_ref(v_self_3769_);
lean_inc(v_size_3771_);
v___y_3666_ = v_hasLambdas_3772_;
v___y_3667_ = v___y_3755_;
v___y_3668_ = v___y_3754_;
v___y_3669_ = v___y_3756_;
v___y_3670_ = v_size_3771_;
v___y_3671_ = v_fns_u2082_3758_;
v___y_3672_ = v_self_3769_;
v___y_3673_ = v_root_3776_;
v___y_3674_ = v_heqProofs_3773_;
v___y_3675_ = v___y_3757_;
v___y_3676_ = v_a_3775_;
v___y_3677_ = v_next_3770_;
v___y_3678_ = v___y_3759_;
v___y_3679_ = v___y_3760_;
v___y_3680_ = v___y_3761_;
v___y_3681_ = v___y_3762_;
v___y_3682_ = v___y_3763_;
v___y_3683_ = v___y_3764_;
v___y_3684_ = v___y_3765_;
v___y_3685_ = v___y_3766_;
v___y_3686_ = v___y_3767_;
v___y_3687_ = v___y_3768_;
goto v___jp_3665_;
}
else
{
lean_object* v_inheritedTraceOptions_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_inheritedTraceOptions_3781_ = lean_ctor_get(v_toCold_3778_, 11);
v___x_3782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3781_, v_options_3779_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_inc_ref(v_next_3770_);
lean_inc_ref(v_self_3769_);
lean_inc(v_size_3771_);
v___y_3666_ = v_hasLambdas_3772_;
v___y_3667_ = v___y_3755_;
v___y_3668_ = v___y_3754_;
v___y_3669_ = v___y_3756_;
v___y_3670_ = v_size_3771_;
v___y_3671_ = v_fns_u2082_3758_;
v___y_3672_ = v_self_3769_;
v___y_3673_ = v_root_3776_;
v___y_3674_ = v_heqProofs_3773_;
v___y_3675_ = v___y_3757_;
v___y_3676_ = v_a_3775_;
v___y_3677_ = v_next_3770_;
v___y_3678_ = v___y_3759_;
v___y_3679_ = v___y_3760_;
v___y_3680_ = v___y_3761_;
v___y_3681_ = v___y_3762_;
v___y_3682_ = v___y_3763_;
v___y_3683_ = v___y_3764_;
v___y_3684_ = v___y_3765_;
v___y_3685_ = v___y_3766_;
v___y_3686_ = v___y_3767_;
v___y_3687_ = v___y_3768_;
goto v___jp_3665_;
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = l_Lean_Meta_Grind_updateLastTag(v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; 
lean_dec_ref_known(v___x_3784_, 1);
lean_inc_ref(v_lhs_3492_);
v___x_3785_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3492_, v___y_3759_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
lean_inc_ref(v_root_3776_);
v___x_3787_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3776_, v___y_3759_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3787_, 1);
v___x_3789_ = lean_st_ref_get(v___y_3759_);
lean_inc_ref(v_lhs_3492_);
v___x_3790_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3789_, v_lhs_3492_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___x_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3792_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3791_, v___y_3759_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3795_, 0, v_a_3786_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v_a_3788_);
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
lean_ctor_set(v___x_3799_, 1, v_a_3793_);
v___x_3800_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3752_, v___x_3799_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_dec_ref_known(v___x_3800_, 1);
lean_inc_ref(v_next_3770_);
lean_inc_ref(v_self_3769_);
lean_inc(v_size_3771_);
v___y_3666_ = v_hasLambdas_3772_;
v___y_3667_ = v___y_3755_;
v___y_3668_ = v___y_3754_;
v___y_3669_ = v___y_3756_;
v___y_3670_ = v_size_3771_;
v___y_3671_ = v_fns_u2082_3758_;
v___y_3672_ = v_self_3769_;
v___y_3673_ = v_root_3776_;
v___y_3674_ = v_heqProofs_3773_;
v___y_3675_ = v___y_3757_;
v___y_3676_ = v_a_3775_;
v___y_3677_ = v_next_3770_;
v___y_3678_ = v___y_3759_;
v___y_3679_ = v___y_3760_;
v___y_3680_ = v___y_3761_;
v___y_3681_ = v___y_3762_;
v___y_3682_ = v___y_3763_;
v___y_3683_ = v___y_3764_;
v___y_3684_ = v___y_3765_;
v___y_3685_ = v___y_3766_;
v___y_3686_ = v___y_3767_;
v___y_3687_ = v___y_3768_;
goto v___jp_3665_;
}
else
{
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
return v___x_3800_;
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_a_3788_);
lean_dec(v_a_3786_);
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
v_a_3801_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3792_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3792_);
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
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3788_);
lean_dec(v_a_3786_);
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
v_a_3809_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3790_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3790_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v_a_3786_);
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
v_a_3817_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3787_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3787_);
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
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
v_a_3825_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3785_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3785_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
return v___x_3784_;
}
}
}
}
else
{
lean_dec_ref(v_root_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_lhs_3492_);
return v___x_3777_;
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v_fns_u2082_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
v_a_3833_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3774_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3774_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
v___jp_3841_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = lean_array_get_size(v___y_3842_);
v___x_3857_ = lean_unsigned_to_nat(0u);
v___x_3858_ = lean_nat_dec_eq(v___x_3856_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v_self_3859_; lean_object* v___x_3860_; 
v_self_3859_ = lean_ctor_get(v_lhsRoot_3496_, 0);
lean_inc_ref(v_self_3859_);
v___x_3860_ = l_Lean_Meta_Grind_getFnRoots(v_self_3859_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___y_3754_ = v_fns_u2081_3845_;
v___y_3755_ = v___y_3842_;
v___y_3756_ = v___y_3843_;
v___y_3757_ = v___y_3844_;
v_fns_u2082_3758_ = v_a_3861_;
v___y_3759_ = v___y_3846_;
v___y_3760_ = v___y_3847_;
v___y_3761_ = v___y_3848_;
v___y_3762_ = v___y_3849_;
v___y_3763_ = v___y_3850_;
v___y_3764_ = v___y_3851_;
v___y_3765_ = v___y_3852_;
v___y_3766_ = v___y_3853_;
v___y_3767_ = v___y_3854_;
v___y_3768_ = v___y_3855_;
goto v___jp_3753_;
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_fns_u2081_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
v_a_3862_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3860_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3860_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v___x_3870_; 
v___x_3870_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3754_ = v_fns_u2081_3845_;
v___y_3755_ = v___y_3842_;
v___y_3756_ = v___y_3843_;
v___y_3757_ = v___y_3844_;
v_fns_u2082_3758_ = v___x_3870_;
v___y_3759_ = v___y_3846_;
v___y_3760_ = v___y_3847_;
v___y_3761_ = v___y_3848_;
v___y_3762_ = v___y_3849_;
v___y_3763_ = v___y_3850_;
v___y_3764_ = v___y_3851_;
v___y_3765_ = v___y_3852_;
v___y_3766_ = v___y_3853_;
v___y_3767_ = v___y_3854_;
v___y_3768_ = v___y_3855_;
goto v___jp_3753_;
}
}
v___jp_3871_:
{
lean_object* v___x_3882_; 
lean_inc_ref(v_lhs_3492_);
v___x_3882_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3492_, v___y_3872_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3950_; 
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v___x_3882_, 0);
lean_dec(v_unused_3951_);
v___x_3884_ = v___x_3882_;
v_isShared_3885_ = v_isSharedCheck_3950_;
goto v_resetjp_3883_;
}
else
{
lean_dec(v___x_3882_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3950_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_self_3886_; lean_object* v_next_3887_; lean_object* v_root_3888_; lean_object* v_congr_3889_; lean_object* v_size_3890_; uint8_t v_interpreted_3891_; uint8_t v_ctor_3892_; uint8_t v_hasLambdas_3893_; uint8_t v_heqProofs_3894_; lean_object* v_idx_3895_; lean_object* v_generation_3896_; lean_object* v_mt_3897_; lean_object* v_sTerms_3898_; uint8_t v_funCC_3899_; lean_object* v_ematchDiagSource_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3947_; 
v_self_3886_ = lean_ctor_get(v_lhsNode_3494_, 0);
v_next_3887_ = lean_ctor_get(v_lhsNode_3494_, 1);
v_root_3888_ = lean_ctor_get(v_lhsNode_3494_, 2);
v_congr_3889_ = lean_ctor_get(v_lhsNode_3494_, 3);
v_size_3890_ = lean_ctor_get(v_lhsNode_3494_, 6);
v_interpreted_3891_ = lean_ctor_get_uint8(v_lhsNode_3494_, sizeof(void*)*12 + 1);
v_ctor_3892_ = lean_ctor_get_uint8(v_lhsNode_3494_, sizeof(void*)*12 + 2);
v_hasLambdas_3893_ = lean_ctor_get_uint8(v_lhsNode_3494_, sizeof(void*)*12 + 3);
v_heqProofs_3894_ = lean_ctor_get_uint8(v_lhsNode_3494_, sizeof(void*)*12 + 4);
v_idx_3895_ = lean_ctor_get(v_lhsNode_3494_, 7);
v_generation_3896_ = lean_ctor_get(v_lhsNode_3494_, 8);
v_mt_3897_ = lean_ctor_get(v_lhsNode_3494_, 9);
v_sTerms_3898_ = lean_ctor_get(v_lhsNode_3494_, 10);
v_funCC_3899_ = lean_ctor_get_uint8(v_lhsNode_3494_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3900_ = lean_ctor_get(v_lhsNode_3494_, 11);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_lhsNode_3494_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3948_ = lean_ctor_get(v_lhsNode_3494_, 5);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_lhsNode_3494_, 4);
lean_dec(v_unused_3949_);
v___x_3902_ = v_lhsNode_3494_;
v_isShared_3903_ = v_isSharedCheck_3947_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_ematchDiagSource_3900_);
lean_inc(v_sTerms_3898_);
lean_inc(v_mt_3897_);
lean_inc(v_generation_3896_);
lean_inc(v_idx_3895_);
lean_inc(v_size_3890_);
lean_inc(v_congr_3889_);
lean_inc(v_root_3888_);
lean_inc(v_next_3887_);
lean_inc(v_self_3886_);
lean_dec(v_lhsNode_3494_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3947_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
lean_ctor_set(v___x_3884_, 0, v_rhs_3493_);
v___x_3905_ = v___x_3884_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_rhs_3493_);
v___x_3905_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v_proof_3490_);
lean_inc_ref(v_root_3888_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 5, v___x_3906_);
lean_ctor_set(v___x_3902_, 4, v___x_3905_);
v___x_3908_ = v___x_3902_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_self_3886_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_next_3887_);
lean_ctor_set(v_reuseFailAlloc_3945_, 2, v_root_3888_);
lean_ctor_set(v_reuseFailAlloc_3945_, 3, v_congr_3889_);
lean_ctor_set(v_reuseFailAlloc_3945_, 4, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3945_, 5, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3945_, 6, v_size_3890_);
lean_ctor_set(v_reuseFailAlloc_3945_, 7, v_idx_3895_);
lean_ctor_set(v_reuseFailAlloc_3945_, 8, v_generation_3896_);
lean_ctor_set(v_reuseFailAlloc_3945_, 9, v_mt_3897_);
lean_ctor_set(v_reuseFailAlloc_3945_, 10, v_sTerms_3898_);
lean_ctor_set(v_reuseFailAlloc_3945_, 11, v_ematchDiagSource_3900_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, sizeof(void*)*12 + 1, v_interpreted_3891_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, sizeof(void*)*12 + 2, v_ctor_3892_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, sizeof(void*)*12 + 3, v_hasLambdas_3893_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, sizeof(void*)*12 + 4, v_heqProofs_3894_);
lean_ctor_set_uint8(v_reuseFailAlloc_3945_, sizeof(void*)*12 + 5, v_funCC_3899_);
v___x_3908_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; 
lean_ctor_set_uint8(v___x_3908_, sizeof(void*)*12, v_flipped_3498_);
lean_inc_ref(v_lhs_3492_);
v___x_3909_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3492_, v___x_3908_, v___y_3872_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref_known(v___x_3909_, 1);
v___x_3910_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3496_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3497_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_array_get_size(v_a_3911_);
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = lean_nat_dec_eq(v___x_3914_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v_self_3917_; lean_object* v___x_3918_; 
v_self_3917_ = lean_ctor_get(v_rhsRoot_3497_, 0);
lean_inc_ref(v_self_3917_);
v___x_3918_ = l_Lean_Meta_Grind_getFnRoots(v_self_3917_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___y_3842_ = v_a_3913_;
v___y_3843_ = v_a_3911_;
v___y_3844_ = v_root_3888_;
v_fns_u2081_3845_ = v_a_3919_;
v___y_3846_ = v___y_3872_;
v___y_3847_ = v___y_3873_;
v___y_3848_ = v___y_3874_;
v___y_3849_ = v___y_3875_;
v___y_3850_ = v___y_3876_;
v___y_3851_ = v___y_3877_;
v___y_3852_ = v___y_3878_;
v___y_3853_ = v___y_3879_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___y_3881_;
goto v___jp_3841_;
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_a_3913_);
lean_dec(v_a_3911_);
lean_dec_ref(v_root_3888_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
v_a_3920_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3918_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3918_);
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
lean_object* v___x_3928_; 
v___x_3928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3842_ = v_a_3913_;
v___y_3843_ = v_a_3911_;
v___y_3844_ = v_root_3888_;
v_fns_u2081_3845_ = v___x_3928_;
v___y_3846_ = v___y_3872_;
v___y_3847_ = v___y_3873_;
v___y_3848_ = v___y_3874_;
v___y_3849_ = v___y_3875_;
v___y_3850_ = v___y_3876_;
v___y_3851_ = v___y_3877_;
v___y_3852_ = v___y_3878_;
v___y_3853_ = v___y_3879_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___y_3881_;
goto v___jp_3841_;
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3911_);
lean_dec_ref(v_root_3888_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
v_a_3929_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3912_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3912_);
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
lean_dec_ref(v_root_3888_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
v_a_3937_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3910_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3910_);
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
lean_dec_ref(v_root_3888_);
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhs_3492_);
return v___x_3909_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3497_);
lean_dec_ref(v_lhsRoot_3496_);
lean_dec_ref(v_rhsNode_3495_);
lean_dec_ref(v_lhsNode_3494_);
lean_dec_ref(v_rhs_3493_);
lean_dec_ref(v_lhs_3492_);
lean_dec_ref(v_proof_3490_);
return v___x_3882_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_3490_ = stack[0].m_obj;
uint8_t v_isHEq_3491_ = stack[1].m_num;
lean_object* v_lhs_3492_ = stack[2].m_obj;
lean_object* v_rhs_3493_ = stack[3].m_obj;
lean_object* v_lhsNode_3494_ = stack[4].m_obj;
lean_object* v_rhsNode_3495_ = stack[5].m_obj;
lean_object* v_lhsRoot_3496_ = stack[6].m_obj;
lean_object* v_rhsRoot_3497_ = stack[7].m_obj;
uint8_t v_flipped_3498_ = stack[8].m_num;
lean_object* v_a_3499_ = stack[9].m_obj;
lean_object* v_a_3500_ = stack[10].m_obj;
lean_object* v_a_3501_ = stack[11].m_obj;
lean_object* v_a_3502_ = stack[12].m_obj;
lean_object* v_a_3503_ = stack[13].m_obj;
lean_object* v_a_3504_ = stack[14].m_obj;
lean_object* v_a_3505_ = stack[15].m_obj;
lean_object* v_a_3506_ = stack[16].m_obj;
lean_object* v_a_3507_ = stack[17].m_obj;
lean_object* v_a_3508_ = stack[18].m_obj;
lean_object* v_res_3981_;
v_res_3981_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3490_, v_isHEq_3491_, v_lhs_3492_, v_rhs_3493_, v_lhsNode_3494_, v_rhsNode_3495_, v_lhsRoot_3496_, v_rhsRoot_3497_, v_flipped_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
stack->m_obj
 = v_res_3981_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3982_ = _args[0];
lean_object* v_isHEq_3983_ = _args[1];
lean_object* v_lhs_3984_ = _args[2];
lean_object* v_rhs_3985_ = _args[3];
lean_object* v_lhsNode_3986_ = _args[4];
lean_object* v_rhsNode_3987_ = _args[5];
lean_object* v_lhsRoot_3988_ = _args[6];
lean_object* v_rhsRoot_3989_ = _args[7];
lean_object* v_flipped_3990_ = _args[8];
lean_object* v_a_3991_ = _args[9];
lean_object* v_a_3992_ = _args[10];
lean_object* v_a_3993_ = _args[11];
lean_object* v_a_3994_ = _args[12];
lean_object* v_a_3995_ = _args[13];
lean_object* v_a_3996_ = _args[14];
lean_object* v_a_3997_ = _args[15];
lean_object* v_a_3998_ = _args[16];
lean_object* v_a_3999_ = _args[17];
lean_object* v_a_4000_ = _args[18];
lean_object* v_a_4001_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_4002_; uint8_t v_flipped_boxed_4003_; lean_object* v_res_4004_; 
v_isHEq_boxed_4002_ = lean_unbox(v_isHEq_3983_);
v_flipped_boxed_4003_ = lean_unbox(v_flipped_3990_);
v_res_4004_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3982_, v_isHEq_boxed_4002_, v_lhs_3984_, v_rhs_3985_, v_lhsNode_3986_, v_rhsNode_3987_, v_lhsRoot_3988_, v_rhsRoot_3989_, v_flipped_boxed_4003_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec(v_a_3991_);
return v_res_4004_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_4005_, lean_object* v_as_x27_4006_, lean_object* v_b_4007_, lean_object* v_a_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_4006_, v_b_4007_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
return v___x_4020_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4005_ = stack[0].m_obj;
lean_object* v_as_x27_4006_ = stack[1].m_obj;
lean_object* v_b_4007_ = stack[2].m_obj;
lean_object* v___y_4009_ = stack[4].m_obj;
lean_object* v___y_4010_ = stack[5].m_obj;
lean_object* v___y_4011_ = stack[6].m_obj;
lean_object* v___y_4012_ = stack[7].m_obj;
lean_object* v___y_4013_ = stack[8].m_obj;
lean_object* v___y_4014_ = stack[9].m_obj;
lean_object* v___y_4015_ = stack[10].m_obj;
lean_object* v___y_4016_ = stack[11].m_obj;
lean_object* v___y_4017_ = stack[12].m_obj;
lean_object* v___y_4018_ = stack[13].m_obj;
lean_object* v_res_4021_;
v_res_4021_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_4005_, v_as_x27_4006_, v_b_4007_, lean_box(0), v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
stack->m_obj
 = v_res_4021_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_4022_, lean_object* v_as_x27_4023_, lean_object* v_b_4024_, lean_object* v_a_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_4022_, v_as_x27_4023_, v_b_4024_, v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec(v_as_x27_4023_);
lean_dec(v_as_4022_);
return v_res_4037_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_4038_, lean_object* v_as_x27_4039_, lean_object* v_b_4040_, lean_object* v_a_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_4039_, v_b_4040_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4053_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4038_ = stack[0].m_obj;
lean_object* v_as_x27_4039_ = stack[1].m_obj;
lean_object* v_b_4040_ = stack[2].m_obj;
lean_object* v___y_4042_ = stack[4].m_obj;
lean_object* v___y_4043_ = stack[5].m_obj;
lean_object* v___y_4044_ = stack[6].m_obj;
lean_object* v___y_4045_ = stack[7].m_obj;
lean_object* v___y_4046_ = stack[8].m_obj;
lean_object* v___y_4047_ = stack[9].m_obj;
lean_object* v___y_4048_ = stack[10].m_obj;
lean_object* v___y_4049_ = stack[11].m_obj;
lean_object* v___y_4050_ = stack[12].m_obj;
lean_object* v___y_4051_ = stack[13].m_obj;
lean_object* v_res_4054_;
v_res_4054_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4038_, v_as_x27_4039_, v_b_4040_, lean_box(0), v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
stack->m_obj
 = v_res_4054_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_4055_, lean_object* v_as_x27_4056_, lean_object* v_b_4057_, lean_object* v_a_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_4055_, v_as_x27_4056_, v_b_4057_, v_a_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec(v_as_x27_4056_);
lean_dec(v_as_4055_);
return v_res_4070_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4079_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4080_ = l_Lean_Name_append(v___x_4079_, v___x_4078_);
return v___x_4080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
return v___x_4086_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4087_, lean_object* v_rhs_4088_, lean_object* v_proof_4089_, uint8_t v_isHEq_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_st_ref_get(v_a_4091_);
lean_inc_ref(v_lhs_4087_);
v___x_4106_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4105_, v_lhs_4087_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
lean_dec(v___x_4105_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = lean_st_ref_get(v_a_4091_);
lean_inc_ref(v_rhs_4088_);
v___x_4109_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4108_, v_rhs_4088_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
lean_dec(v___x_4108_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v_root_4111_; lean_object* v_root_4112_; size_t v___x_4113_; size_t v___x_4114_; uint8_t v___x_4115_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v_root_4111_ = lean_ctor_get(v_a_4107_, 2);
v_root_4112_ = lean_ctor_get(v_a_4110_, 2);
v___x_4113_ = lean_ptr_addr(v_root_4111_);
v___x_4114_ = lean_ptr_addr(v_root_4112_);
v___x_4115_ = lean_usize_dec_eq(v___x_4113_, v___x_4114_);
if (v___x_4115_ == 0)
{
lean_object* v_toCold_4116_; lean_object* v_options_4117_; lean_object* v_inheritedTraceOptions_4118_; uint8_t v_hasTrace_4119_; uint8_t v___x_4120_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4158_; lean_object* v___y_4159_; uint8_t v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4186_; lean_object* v___y_4187_; uint8_t v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4216_; uint8_t v___y_4217_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; uint8_t v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; uint8_t v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; uint8_t v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; uint8_t v___y_4272_; lean_object* v___y_4273_; lean_object* v_size_4274_; uint8_t v_interpreted_4275_; uint8_t v_ctor_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; uint8_t v___y_4287_; lean_object* v___y_4288_; uint8_t v_ctor_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; uint8_t v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4306_; lean_object* v___y_4307_; uint8_t v_valueInconsistency_4308_; uint8_t v_trueEqFalse_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4339_; lean_object* v___y_4340_; uint8_t v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; 
v_toCold_4116_ = lean_ctor_get(v_a_4099_, 0);
v_options_4117_ = lean_ctor_get(v_toCold_4116_, 2);
v_inheritedTraceOptions_4118_ = lean_ctor_get(v_toCold_4116_, 11);
v_hasTrace_4119_ = lean_ctor_get_uint8(v_options_4117_, sizeof(void*)*1);
v___x_4120_ = 1;
if (v_hasTrace_4119_ == 0)
{
v___y_4366_ = v_a_4091_;
v___y_4367_ = v_a_4092_;
v___y_4368_ = v_a_4093_;
v___y_4369_ = v_a_4094_;
v___y_4370_ = v_a_4095_;
v___y_4371_ = v_a_4096_;
v___y_4372_ = v_a_4097_;
v___y_4373_ = v_a_4098_;
v___y_4374_ = v_a_4099_;
v___y_4375_ = v_a_4100_;
goto v___jp_4365_;
}
else
{
lean_object* v___x_4409_; lean_object* v_____do__lift_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4118_, v_options_4117_, v___x_4424_);
if (v___x_4425_ == 0)
{
v___y_4366_ = v_a_4091_;
v___y_4367_ = v_a_4092_;
v___y_4368_ = v_a_4093_;
v___y_4369_ = v_a_4094_;
v___y_4370_ = v_a_4095_;
v___y_4371_ = v_a_4096_;
v___y_4372_ = v_a_4097_;
v___y_4373_ = v_a_4098_;
v___y_4374_ = v_a_4099_;
v___y_4375_ = v_a_4100_;
goto v___jp_4365_;
}
else
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_Grind_updateLastTag(v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_dec_ref_known(v___x_4426_, 1);
if (v_isHEq_4090_ == 0)
{
lean_object* v___x_4427_; 
lean_inc_ref(v_rhs_4088_);
lean_inc_ref(v_lhs_4087_);
v___x_4427_ = l_Lean_Meta_mkEq(v_lhs_4087_, v_rhs_4088_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v_____do__lift_4411_ = v_a_4428_;
v___y_4412_ = v_a_4091_;
v___y_4413_ = v_a_4092_;
v___y_4414_ = v_a_4093_;
v___y_4415_ = v_a_4094_;
v___y_4416_ = v_a_4095_;
v___y_4417_ = v_a_4096_;
v___y_4418_ = v_a_4097_;
v___y_4419_ = v_a_4098_;
v___y_4420_ = v_a_4099_;
v___y_4421_ = v_a_4100_;
goto v___jp_4410_;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4429_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4427_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4427_);
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
lean_object* v___x_4437_; 
lean_inc_ref(v_rhs_4088_);
lean_inc_ref(v_lhs_4087_);
v___x_4437_ = l_Lean_Meta_mkHEq(v_lhs_4087_, v_rhs_4088_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4438_);
lean_dec_ref_known(v___x_4437_, 1);
v_____do__lift_4411_ = v_a_4438_;
v___y_4412_ = v_a_4091_;
v___y_4413_ = v_a_4092_;
v___y_4414_ = v_a_4093_;
v___y_4415_ = v_a_4094_;
v___y_4416_ = v_a_4095_;
v___y_4417_ = v_a_4096_;
v___y_4418_ = v_a_4097_;
v___y_4419_ = v_a_4098_;
v___y_4420_ = v_a_4099_;
v___y_4421_ = v_a_4100_;
goto v___jp_4410_;
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4439_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4437_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4437_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
}
else
{
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
return v___x_4426_;
}
}
v___jp_4410_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = l_Lean_MessageData_ofExpr(v_____do__lift_4411_);
v___x_4423_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4409_, v___x_4422_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref_known(v___x_4423_, 1);
v___y_4366_ = v___y_4412_;
v___y_4367_ = v___y_4413_;
v___y_4368_ = v___y_4414_;
v___y_4369_ = v___y_4415_;
v___y_4370_ = v___y_4416_;
v___y_4371_ = v___y_4417_;
v___y_4372_ = v___y_4418_;
v___y_4373_ = v___y_4419_;
v___y_4374_ = v___y_4420_;
v___y_4375_ = v___y_4421_;
goto v___jp_4365_;
}
else
{
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
return v___x_4423_;
}
}
}
v___jp_4121_:
{
lean_object* v_toCold_4132_; lean_object* v_options_4133_; uint8_t v_hasTrace_4134_; 
v_toCold_4132_ = lean_ctor_get(v___y_4130_, 0);
v_options_4133_ = lean_ctor_get(v_toCold_4132_, 2);
v_hasTrace_4134_ = lean_ctor_get_uint8(v_options_4133_, sizeof(void*)*1);
if (v_hasTrace_4134_ == 0)
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Meta_Grind_checkInvariants(v___x_4115_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4135_;
}
else
{
lean_object* v_inheritedTraceOptions_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v_inheritedTraceOptions_4136_ = lean_ctor_get(v_toCold_4132_, 11);
v___x_4137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4136_, v_options_4133_, v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_Grind_checkInvariants(v___x_4115_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4140_;
}
else
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_Grind_updateLastTag(v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_dec_ref_known(v___x_4141_, 1);
v___x_4142_ = lean_st_ref_get(v___y_4122_);
v___x_4143_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4142_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___x_4142_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v_a_4144_);
v___x_4147_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4137_, v___x_4146_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v___x_4148_; 
lean_dec_ref_known(v___x_4147_, 1);
v___x_4148_ = l_Lean_Meta_Grind_checkInvariants(v___x_4115_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4148_;
}
else
{
return v___x_4147_;
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4143_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4143_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
else
{
return v___x_4141_;
}
}
}
}
v___jp_4157_:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4161_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; uint8_t v___x_4173_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v___x_4173_ = lean_unbox(v_a_4172_);
lean_dec(v_a_4172_);
if (v___x_4173_ == 0)
{
if (v___y_4160_ == 0)
{
lean_dec_ref(v___y_4159_);
lean_dec_ref(v___y_4158_);
v___y_4122_ = v___y_4161_;
v___y_4123_ = v___y_4162_;
v___y_4124_ = v___y_4163_;
v___y_4125_ = v___y_4164_;
v___y_4126_ = v___y_4165_;
v___y_4127_ = v___y_4166_;
v___y_4128_ = v___y_4167_;
v___y_4129_ = v___y_4168_;
v___y_4130_ = v___y_4169_;
v___y_4131_ = v___y_4170_;
goto v___jp_4121_;
}
else
{
lean_object* v_self_4174_; lean_object* v_self_4175_; lean_object* v___x_4176_; 
v_self_4174_ = lean_ctor_get(v___y_4159_, 0);
lean_inc_ref(v_self_4174_);
lean_dec_ref(v___y_4159_);
v_self_4175_ = lean_ctor_get(v___y_4158_, 0);
lean_inc_ref(v_self_4175_);
lean_dec_ref(v___y_4158_);
v___x_4176_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4174_, v_self_4175_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_dec_ref_known(v___x_4176_, 1);
v___y_4122_ = v___y_4161_;
v___y_4123_ = v___y_4162_;
v___y_4124_ = v___y_4163_;
v___y_4125_ = v___y_4164_;
v___y_4126_ = v___y_4165_;
v___y_4127_ = v___y_4166_;
v___y_4128_ = v___y_4167_;
v___y_4129_ = v___y_4168_;
v___y_4130_ = v___y_4169_;
v___y_4131_ = v___y_4170_;
goto v___jp_4121_;
}
else
{
return v___x_4176_;
}
}
}
else
{
lean_dec_ref(v___y_4159_);
lean_dec_ref(v___y_4158_);
v___y_4122_ = v___y_4161_;
v___y_4123_ = v___y_4162_;
v___y_4124_ = v___y_4163_;
v___y_4125_ = v___y_4164_;
v___y_4126_ = v___y_4165_;
v___y_4127_ = v___y_4166_;
v___y_4128_ = v___y_4167_;
v___y_4129_ = v___y_4168_;
v___y_4130_ = v___y_4169_;
v___y_4131_ = v___y_4170_;
goto v___jp_4121_;
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec_ref(v___y_4159_);
lean_dec_ref(v___y_4158_);
v_a_4177_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4171_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4171_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
v___jp_4185_:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4189_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; uint8_t v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = lean_unbox(v_a_4200_);
lean_dec(v_a_4200_);
if (v___x_4201_ == 0)
{
uint8_t v_ctor_4202_; 
v_ctor_4202_ = lean_ctor_get_uint8(v___y_4187_, sizeof(void*)*12 + 2);
if (v_ctor_4202_ == 0)
{
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4187_;
v___y_4160_ = v___y_4188_;
v___y_4161_ = v___y_4189_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4191_;
v___y_4164_ = v___y_4192_;
v___y_4165_ = v___y_4193_;
v___y_4166_ = v___y_4194_;
v___y_4167_ = v___y_4195_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
goto v___jp_4157_;
}
else
{
uint8_t v_ctor_4203_; 
v_ctor_4203_ = lean_ctor_get_uint8(v___y_4186_, sizeof(void*)*12 + 2);
if (v_ctor_4203_ == 0)
{
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4187_;
v___y_4160_ = v___y_4188_;
v___y_4161_ = v___y_4189_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4191_;
v___y_4164_ = v___y_4192_;
v___y_4165_ = v___y_4193_;
v___y_4166_ = v___y_4194_;
v___y_4167_ = v___y_4195_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
goto v___jp_4157_;
}
else
{
lean_object* v_self_4204_; lean_object* v_self_4205_; lean_object* v___x_4206_; 
v_self_4204_ = lean_ctor_get(v___y_4187_, 0);
v_self_4205_ = lean_ctor_get(v___y_4186_, 0);
lean_inc_ref(v_self_4205_);
lean_inc_ref(v_self_4204_);
v___x_4206_ = l_Lean_Meta_Grind_propagateCtor(v_self_4204_, v_self_4205_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_dec_ref_known(v___x_4206_, 1);
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4187_;
v___y_4160_ = v___y_4188_;
v___y_4161_ = v___y_4189_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4191_;
v___y_4164_ = v___y_4192_;
v___y_4165_ = v___y_4193_;
v___y_4166_ = v___y_4194_;
v___y_4167_ = v___y_4195_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
goto v___jp_4157_;
}
else
{
lean_dec_ref(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v___x_4206_;
}
}
}
}
else
{
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4187_;
v___y_4160_ = v___y_4188_;
v___y_4161_ = v___y_4189_;
v___y_4162_ = v___y_4190_;
v___y_4163_ = v___y_4191_;
v___y_4164_ = v___y_4192_;
v___y_4165_ = v___y_4193_;
v___y_4166_ = v___y_4194_;
v___y_4167_ = v___y_4195_;
v___y_4168_ = v___y_4196_;
v___y_4169_ = v___y_4197_;
v___y_4170_ = v___y_4198_;
goto v___jp_4157_;
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v___y_4187_);
lean_dec_ref(v___y_4186_);
v_a_4207_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4199_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4199_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
v___jp_4215_:
{
if (v___y_4217_ == 0)
{
v___y_4186_ = v___y_4216_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4226_;
v___y_4196_ = v___y_4227_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4229_;
goto v___jp_4185_;
}
else
{
lean_object* v___x_4230_; 
v___x_4230_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_dec_ref_known(v___x_4230_, 1);
v___y_4186_ = v___y_4216_;
v___y_4187_ = v___y_4218_;
v___y_4188_ = v___y_4219_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4221_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4223_;
v___y_4193_ = v___y_4224_;
v___y_4194_ = v___y_4225_;
v___y_4195_ = v___y_4226_;
v___y_4196_ = v___y_4227_;
v___y_4197_ = v___y_4228_;
v___y_4198_ = v___y_4229_;
goto v___jp_4185_;
}
else
{
lean_dec_ref(v___y_4218_);
lean_dec_ref(v___y_4216_);
return v___x_4230_;
}
}
}
v___jp_4231_:
{
lean_object* v___x_4246_; 
lean_inc_ref(v___y_4236_);
lean_inc_ref(v___y_4241_);
v___x_4246_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4089_, v_isHEq_4090_, v_rhs_4088_, v_lhs_4087_, v_a_4110_, v_a_4107_, v___y_4241_, v___y_4236_, v___x_4120_, v___y_4242_, v___y_4243_, v___y_4237_, v___y_4232_, v___y_4244_, v___y_4245_, v___y_4233_, v___y_4238_, v___y_4234_, v___y_4239_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_dec_ref_known(v___x_4246_, 1);
v___y_4216_ = v___y_4241_;
v___y_4217_ = v___y_4235_;
v___y_4218_ = v___y_4236_;
v___y_4219_ = v___y_4240_;
v___y_4220_ = v___y_4242_;
v___y_4221_ = v___y_4243_;
v___y_4222_ = v___y_4237_;
v___y_4223_ = v___y_4232_;
v___y_4224_ = v___y_4244_;
v___y_4225_ = v___y_4245_;
v___y_4226_ = v___y_4233_;
v___y_4227_ = v___y_4238_;
v___y_4228_ = v___y_4234_;
v___y_4229_ = v___y_4239_;
goto v___jp_4215_;
}
else
{
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___y_4236_);
return v___x_4246_;
}
}
v___jp_4247_:
{
lean_object* v___x_4262_; 
lean_inc_ref(v___y_4257_);
lean_inc_ref(v___y_4252_);
v___x_4262_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4089_, v_isHEq_4090_, v_lhs_4087_, v_rhs_4088_, v_a_4107_, v_a_4110_, v___y_4252_, v___y_4257_, v___x_4115_, v___y_4258_, v___y_4259_, v___y_4253_, v___y_4248_, v___y_4260_, v___y_4261_, v___y_4249_, v___y_4254_, v___y_4250_, v___y_4255_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_dec_ref_known(v___x_4262_, 1);
v___y_4216_ = v___y_4257_;
v___y_4217_ = v___y_4251_;
v___y_4218_ = v___y_4252_;
v___y_4219_ = v___y_4256_;
v___y_4220_ = v___y_4258_;
v___y_4221_ = v___y_4259_;
v___y_4222_ = v___y_4253_;
v___y_4223_ = v___y_4248_;
v___y_4224_ = v___y_4260_;
v___y_4225_ = v___y_4261_;
v___y_4226_ = v___y_4249_;
v___y_4227_ = v___y_4254_;
v___y_4228_ = v___y_4250_;
v___y_4229_ = v___y_4255_;
goto v___jp_4215_;
}
else
{
lean_dec_ref(v___y_4257_);
lean_dec_ref(v___y_4252_);
return v___x_4262_;
}
}
v___jp_4263_:
{
lean_object* v_size_4281_; uint8_t v___x_4282_; 
v_size_4281_ = lean_ctor_get(v___y_4268_, 6);
v___x_4282_ = lean_nat_dec_lt(v_size_4274_, v_size_4281_);
lean_dec(v_size_4274_);
if (v___x_4282_ == 0)
{
v___y_4248_ = v___y_4264_;
v___y_4249_ = v___y_4265_;
v___y_4250_ = v___y_4266_;
v___y_4251_ = v___y_4267_;
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___y_4269_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4271_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4273_;
v___y_4258_ = v___y_4277_;
v___y_4259_ = v___y_4278_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4280_;
goto v___jp_4247_;
}
else
{
if (v_interpreted_4275_ == 0)
{
if (v_ctor_4276_ == 0)
{
v___y_4232_ = v___y_4264_;
v___y_4233_ = v___y_4265_;
v___y_4234_ = v___y_4266_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4268_;
v___y_4237_ = v___y_4269_;
v___y_4238_ = v___y_4270_;
v___y_4239_ = v___y_4271_;
v___y_4240_ = v___y_4272_;
v___y_4241_ = v___y_4273_;
v___y_4242_ = v___y_4277_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4279_;
v___y_4245_ = v___y_4280_;
goto v___jp_4231_;
}
else
{
v___y_4248_ = v___y_4264_;
v___y_4249_ = v___y_4265_;
v___y_4250_ = v___y_4266_;
v___y_4251_ = v___y_4267_;
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___y_4269_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4271_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4273_;
v___y_4258_ = v___y_4277_;
v___y_4259_ = v___y_4278_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4280_;
goto v___jp_4247_;
}
}
else
{
v___y_4248_ = v___y_4264_;
v___y_4249_ = v___y_4265_;
v___y_4250_ = v___y_4266_;
v___y_4251_ = v___y_4267_;
v___y_4252_ = v___y_4268_;
v___y_4253_ = v___y_4269_;
v___y_4254_ = v___y_4270_;
v___y_4255_ = v___y_4271_;
v___y_4256_ = v___y_4272_;
v___y_4257_ = v___y_4273_;
v___y_4258_ = v___y_4277_;
v___y_4259_ = v___y_4278_;
v___y_4260_ = v___y_4279_;
v___y_4261_ = v___y_4280_;
goto v___jp_4247_;
}
}
}
v___jp_4283_:
{
if (v_ctor_4289_ == 0)
{
lean_object* v_size_4299_; uint8_t v_interpreted_4300_; uint8_t v_ctor_4301_; 
v_size_4299_ = lean_ctor_get(v___y_4294_, 6);
lean_inc(v_size_4299_);
v_interpreted_4300_ = lean_ctor_get_uint8(v___y_4294_, sizeof(void*)*12 + 1);
v_ctor_4301_ = lean_ctor_get_uint8(v___y_4294_, sizeof(void*)*12 + 2);
v___y_4264_ = v___y_4284_;
v___y_4265_ = v___y_4285_;
v___y_4266_ = v___y_4286_;
v___y_4267_ = v___y_4287_;
v___y_4268_ = v___y_4288_;
v___y_4269_ = v___y_4290_;
v___y_4270_ = v___y_4291_;
v___y_4271_ = v___y_4292_;
v___y_4272_ = v___y_4293_;
v___y_4273_ = v___y_4294_;
v_size_4274_ = v_size_4299_;
v_interpreted_4275_ = v_interpreted_4300_;
v_ctor_4276_ = v_ctor_4301_;
v___y_4277_ = v___y_4295_;
v___y_4278_ = v___y_4296_;
v___y_4279_ = v___y_4297_;
v___y_4280_ = v___y_4298_;
goto v___jp_4263_;
}
else
{
uint8_t v_ctor_4302_; 
v_ctor_4302_ = lean_ctor_get_uint8(v___y_4294_, sizeof(void*)*12 + 2);
if (v_ctor_4302_ == 0)
{
v___y_4232_ = v___y_4284_;
v___y_4233_ = v___y_4285_;
v___y_4234_ = v___y_4286_;
v___y_4235_ = v___y_4287_;
v___y_4236_ = v___y_4288_;
v___y_4237_ = v___y_4290_;
v___y_4238_ = v___y_4291_;
v___y_4239_ = v___y_4292_;
v___y_4240_ = v___y_4293_;
v___y_4241_ = v___y_4294_;
v___y_4242_ = v___y_4295_;
v___y_4243_ = v___y_4296_;
v___y_4244_ = v___y_4297_;
v___y_4245_ = v___y_4298_;
goto v___jp_4231_;
}
else
{
lean_object* v_size_4303_; uint8_t v_interpreted_4304_; 
v_size_4303_ = lean_ctor_get(v___y_4294_, 6);
lean_inc(v_size_4303_);
v_interpreted_4304_ = lean_ctor_get_uint8(v___y_4294_, sizeof(void*)*12 + 1);
v___y_4264_ = v___y_4284_;
v___y_4265_ = v___y_4285_;
v___y_4266_ = v___y_4286_;
v___y_4267_ = v___y_4287_;
v___y_4268_ = v___y_4288_;
v___y_4269_ = v___y_4290_;
v___y_4270_ = v___y_4291_;
v___y_4271_ = v___y_4292_;
v___y_4272_ = v___y_4293_;
v___y_4273_ = v___y_4294_;
v_size_4274_ = v_size_4303_;
v_interpreted_4275_ = v_interpreted_4304_;
v_ctor_4276_ = v_ctor_4302_;
v___y_4277_ = v___y_4295_;
v___y_4278_ = v___y_4296_;
v___y_4279_ = v___y_4297_;
v___y_4280_ = v___y_4298_;
goto v___jp_4263_;
}
}
}
v___jp_4305_:
{
uint8_t v_interpreted_4320_; 
v_interpreted_4320_ = lean_ctor_get_uint8(v___y_4307_, sizeof(void*)*12 + 1);
if (v_interpreted_4320_ == 0)
{
uint8_t v_ctor_4321_; 
v_ctor_4321_ = lean_ctor_get_uint8(v___y_4307_, sizeof(void*)*12 + 2);
v___y_4284_ = v___y_4313_;
v___y_4285_ = v___y_4316_;
v___y_4286_ = v___y_4318_;
v___y_4287_ = v_trueEqFalse_4309_;
v___y_4288_ = v___y_4307_;
v_ctor_4289_ = v_ctor_4321_;
v___y_4290_ = v___y_4312_;
v___y_4291_ = v___y_4317_;
v___y_4292_ = v___y_4319_;
v___y_4293_ = v_valueInconsistency_4308_;
v___y_4294_ = v___y_4306_;
v___y_4295_ = v___y_4310_;
v___y_4296_ = v___y_4311_;
v___y_4297_ = v___y_4314_;
v___y_4298_ = v___y_4315_;
goto v___jp_4283_;
}
else
{
uint8_t v_interpreted_4322_; 
v_interpreted_4322_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*12 + 1);
if (v_interpreted_4322_ == 0)
{
v___y_4232_ = v___y_4313_;
v___y_4233_ = v___y_4316_;
v___y_4234_ = v___y_4318_;
v___y_4235_ = v_trueEqFalse_4309_;
v___y_4236_ = v___y_4307_;
v___y_4237_ = v___y_4312_;
v___y_4238_ = v___y_4317_;
v___y_4239_ = v___y_4319_;
v___y_4240_ = v_valueInconsistency_4308_;
v___y_4241_ = v___y_4306_;
v___y_4242_ = v___y_4310_;
v___y_4243_ = v___y_4311_;
v___y_4244_ = v___y_4314_;
v___y_4245_ = v___y_4315_;
goto v___jp_4231_;
}
else
{
uint8_t v_ctor_4323_; 
v_ctor_4323_ = lean_ctor_get_uint8(v___y_4307_, sizeof(void*)*12 + 2);
v___y_4284_ = v___y_4313_;
v___y_4285_ = v___y_4316_;
v___y_4286_ = v___y_4318_;
v___y_4287_ = v_trueEqFalse_4309_;
v___y_4288_ = v___y_4307_;
v_ctor_4289_ = v_ctor_4323_;
v___y_4290_ = v___y_4312_;
v___y_4291_ = v___y_4317_;
v___y_4292_ = v___y_4319_;
v___y_4293_ = v_valueInconsistency_4308_;
v___y_4294_ = v___y_4306_;
v___y_4295_ = v___y_4310_;
v___y_4296_ = v___y_4311_;
v___y_4297_ = v___y_4314_;
v___y_4298_ = v___y_4315_;
goto v___jp_4283_;
}
}
}
v___jp_4324_:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4335_, v___y_4330_, v___y_4336_, v___y_4329_, v___y_4326_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_dec_ref_known(v___x_4337_, 1);
v___y_4306_ = v___y_4332_;
v___y_4307_ = v___y_4328_;
v_valueInconsistency_4308_ = v___x_4115_;
v_trueEqFalse_4309_ = v___x_4120_;
v___y_4310_ = v___y_4335_;
v___y_4311_ = v___y_4333_;
v___y_4312_ = v___y_4334_;
v___y_4313_ = v___y_4331_;
v___y_4314_ = v___y_4327_;
v___y_4315_ = v___y_4325_;
v___y_4316_ = v___y_4330_;
v___y_4317_ = v___y_4336_;
v___y_4318_ = v___y_4329_;
v___y_4319_ = v___y_4326_;
goto v___jp_4305_;
}
else
{
lean_dec_ref(v___y_4332_);
lean_dec_ref(v___y_4328_);
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
return v___x_4337_;
}
}
v___jp_4338_:
{
if (v___y_4341_ == 0)
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_Meta_Grind_hasSameType(v___y_4340_, v___y_4343_, v___y_4347_, v___y_4353_, v___y_4346_, v___y_4342_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; uint8_t v___x_4356_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_unbox(v_a_4355_);
lean_dec(v_a_4355_);
if (v___x_4356_ == 0)
{
v___y_4306_ = v___y_4349_;
v___y_4307_ = v___y_4344_;
v_valueInconsistency_4308_ = v___x_4115_;
v_trueEqFalse_4309_ = v___x_4115_;
v___y_4310_ = v___y_4352_;
v___y_4311_ = v___y_4350_;
v___y_4312_ = v___y_4351_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4339_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4353_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4342_;
goto v___jp_4305_;
}
else
{
v___y_4306_ = v___y_4349_;
v___y_4307_ = v___y_4344_;
v_valueInconsistency_4308_ = v___x_4120_;
v_trueEqFalse_4309_ = v___x_4115_;
v___y_4310_ = v___y_4352_;
v___y_4311_ = v___y_4350_;
v___y_4312_ = v___y_4351_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4339_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4353_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4342_;
goto v___jp_4305_;
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4344_);
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4357_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4354_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4354_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
lean_dec_ref(v___y_4343_);
lean_dec_ref(v___y_4340_);
v___y_4306_ = v___y_4349_;
v___y_4307_ = v___y_4344_;
v_valueInconsistency_4308_ = v___x_4120_;
v_trueEqFalse_4309_ = v___x_4115_;
v___y_4310_ = v___y_4352_;
v___y_4311_ = v___y_4350_;
v___y_4312_ = v___y_4351_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4339_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4353_;
v___y_4318_ = v___y_4346_;
v___y_4319_ = v___y_4342_;
goto v___jp_4305_;
}
}
v___jp_4365_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_st_ref_get(v___y_4366_);
lean_inc_ref(v_root_4111_);
v___x_4377_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4376_, v_root_4111_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___x_4376_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = lean_st_ref_get(v___y_4366_);
lean_inc_ref(v_root_4112_);
v___x_4380_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4379_, v_root_4112_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___x_4379_);
if (lean_obj_tag(v___x_4380_) == 0)
{
uint8_t v_interpreted_4381_; 
v_interpreted_4381_ = lean_ctor_get_uint8(v_a_4378_, sizeof(void*)*12 + 1);
if (v_interpreted_4381_ == 0)
{
lean_object* v_a_4382_; uint8_t v_ctor_4383_; 
v_a_4382_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4380_, 1);
v_ctor_4383_ = lean_ctor_get_uint8(v_a_4378_, sizeof(void*)*12 + 2);
v___y_4284_ = v___y_4369_;
v___y_4285_ = v___y_4372_;
v___y_4286_ = v___y_4374_;
v___y_4287_ = v___x_4115_;
v___y_4288_ = v_a_4378_;
v_ctor_4289_ = v_ctor_4383_;
v___y_4290_ = v___y_4368_;
v___y_4291_ = v___y_4373_;
v___y_4292_ = v___y_4375_;
v___y_4293_ = v___x_4115_;
v___y_4294_ = v_a_4382_;
v___y_4295_ = v___y_4366_;
v___y_4296_ = v___y_4367_;
v___y_4297_ = v___y_4370_;
v___y_4298_ = v___y_4371_;
goto v___jp_4283_;
}
else
{
lean_object* v_a_4384_; uint8_t v_interpreted_4385_; 
v_a_4384_ = lean_ctor_get(v___x_4380_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4380_, 1);
v_interpreted_4385_ = lean_ctor_get_uint8(v_a_4384_, sizeof(void*)*12 + 1);
if (v_interpreted_4385_ == 0)
{
v___y_4232_ = v___y_4369_;
v___y_4233_ = v___y_4372_;
v___y_4234_ = v___y_4374_;
v___y_4235_ = v___x_4115_;
v___y_4236_ = v_a_4378_;
v___y_4237_ = v___y_4368_;
v___y_4238_ = v___y_4373_;
v___y_4239_ = v___y_4375_;
v___y_4240_ = v___x_4115_;
v___y_4241_ = v_a_4384_;
v___y_4242_ = v___y_4366_;
v___y_4243_ = v___y_4367_;
v___y_4244_ = v___y_4370_;
v___y_4245_ = v___y_4371_;
goto v___jp_4231_;
}
else
{
lean_object* v_self_4386_; uint8_t v_ctor_4387_; uint8_t v_heqProofs_4388_; lean_object* v_self_4389_; uint8_t v_heqProofs_4390_; uint8_t v___x_4391_; 
v_self_4386_ = lean_ctor_get(v_a_4378_, 0);
v_ctor_4387_ = lean_ctor_get_uint8(v_a_4378_, sizeof(void*)*12 + 2);
v_heqProofs_4388_ = lean_ctor_get_uint8(v_a_4378_, sizeof(void*)*12 + 4);
v_self_4389_ = lean_ctor_get(v_a_4384_, 0);
v_heqProofs_4390_ = lean_ctor_get_uint8(v_a_4384_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4111_);
v___x_4391_ = l_Lean_Expr_isTrue(v_root_4111_);
if (v___x_4391_ == 0)
{
uint8_t v___x_4392_; 
lean_inc_ref(v_root_4112_);
v___x_4392_ = l_Lean_Expr_isTrue(v_root_4112_);
if (v___x_4392_ == 0)
{
if (v_isHEq_4090_ == 0)
{
if (v_heqProofs_4388_ == 0)
{
if (v_heqProofs_4390_ == 0)
{
v___y_4284_ = v___y_4369_;
v___y_4285_ = v___y_4372_;
v___y_4286_ = v___y_4374_;
v___y_4287_ = v___x_4115_;
v___y_4288_ = v_a_4378_;
v_ctor_4289_ = v_ctor_4387_;
v___y_4290_ = v___y_4368_;
v___y_4291_ = v___y_4373_;
v___y_4292_ = v___y_4375_;
v___y_4293_ = v___x_4120_;
v___y_4294_ = v_a_4384_;
v___y_4295_ = v___y_4366_;
v___y_4296_ = v___y_4367_;
v___y_4297_ = v___y_4370_;
v___y_4298_ = v___y_4371_;
goto v___jp_4283_;
}
else
{
lean_inc_ref(v_self_4389_);
lean_inc_ref(v_self_4386_);
v___y_4339_ = v___y_4371_;
v___y_4340_ = v_self_4386_;
v___y_4341_ = v___x_4392_;
v___y_4342_ = v___y_4375_;
v___y_4343_ = v_self_4389_;
v___y_4344_ = v_a_4378_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4374_;
v___y_4347_ = v___y_4372_;
v___y_4348_ = v___y_4369_;
v___y_4349_ = v_a_4384_;
v___y_4350_ = v___y_4367_;
v___y_4351_ = v___y_4368_;
v___y_4352_ = v___y_4366_;
v___y_4353_ = v___y_4373_;
goto v___jp_4338_;
}
}
else
{
lean_inc_ref(v_self_4389_);
lean_inc_ref(v_self_4386_);
v___y_4339_ = v___y_4371_;
v___y_4340_ = v_self_4386_;
v___y_4341_ = v___x_4392_;
v___y_4342_ = v___y_4375_;
v___y_4343_ = v_self_4389_;
v___y_4344_ = v_a_4378_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4374_;
v___y_4347_ = v___y_4372_;
v___y_4348_ = v___y_4369_;
v___y_4349_ = v_a_4384_;
v___y_4350_ = v___y_4367_;
v___y_4351_ = v___y_4368_;
v___y_4352_ = v___y_4366_;
v___y_4353_ = v___y_4373_;
goto v___jp_4338_;
}
}
else
{
lean_inc_ref(v_self_4389_);
lean_inc_ref(v_self_4386_);
v___y_4339_ = v___y_4371_;
v___y_4340_ = v_self_4386_;
v___y_4341_ = v___x_4392_;
v___y_4342_ = v___y_4375_;
v___y_4343_ = v_self_4389_;
v___y_4344_ = v_a_4378_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4374_;
v___y_4347_ = v___y_4372_;
v___y_4348_ = v___y_4369_;
v___y_4349_ = v_a_4384_;
v___y_4350_ = v___y_4367_;
v___y_4351_ = v___y_4368_;
v___y_4352_ = v___y_4366_;
v___y_4353_ = v___y_4373_;
goto v___jp_4338_;
}
}
else
{
v___y_4325_ = v___y_4371_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4370_;
v___y_4328_ = v_a_4378_;
v___y_4329_ = v___y_4374_;
v___y_4330_ = v___y_4372_;
v___y_4331_ = v___y_4369_;
v___y_4332_ = v_a_4384_;
v___y_4333_ = v___y_4367_;
v___y_4334_ = v___y_4368_;
v___y_4335_ = v___y_4366_;
v___y_4336_ = v___y_4373_;
goto v___jp_4324_;
}
}
else
{
v___y_4325_ = v___y_4371_;
v___y_4326_ = v___y_4375_;
v___y_4327_ = v___y_4370_;
v___y_4328_ = v_a_4378_;
v___y_4329_ = v___y_4374_;
v___y_4330_ = v___y_4372_;
v___y_4331_ = v___y_4369_;
v___y_4332_ = v_a_4384_;
v___y_4333_ = v___y_4367_;
v___y_4334_ = v___y_4368_;
v___y_4335_ = v___y_4366_;
v___y_4336_ = v___y_4373_;
goto v___jp_4324_;
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_a_4378_);
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4393_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4380_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4380_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4401_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4377_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4377_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
else
{
lean_object* v_toCold_4447_; lean_object* v_options_4448_; uint8_t v_hasTrace_4449_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
v_toCold_4447_ = lean_ctor_get(v_a_4099_, 0);
v_options_4448_ = lean_ctor_get(v_toCold_4447_, 2);
v_hasTrace_4449_ = lean_ctor_get_uint8(v_options_4448_, sizeof(void*)*1);
if (v_hasTrace_4449_ == 0)
{
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
goto v___jp_4102_;
}
else
{
lean_object* v_inheritedTraceOptions_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v_inheritedTraceOptions_4450_ = lean_ctor_get(v_toCold_4447_, 11);
v___x_4451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4450_, v_options_4448_, v___x_4452_);
if (v___x_4453_ == 0)
{
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
goto v___jp_4102_;
}
else
{
lean_object* v___x_4454_; 
v___x_4454_ = l_Lean_Meta_Grind_updateLastTag(v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; 
lean_dec_ref_known(v___x_4454_, 1);
v___x_4455_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4087_, v_a_4091_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4088_, v_a_4091_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref_known(v___x_4457_, 1);
v___x_4459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v_a_4456_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___x_4461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
lean_ctor_set(v___x_4461_, 1, v_a_4458_);
v___x_4462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4451_, v___x_4463_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_dec_ref_known(v___x_4464_, 1);
goto v___jp_4102_;
}
else
{
return v___x_4464_;
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_a_4456_);
v_a_4465_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4457_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4457_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec_ref(v_rhs_4088_);
v_a_4473_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4455_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4455_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
return v___x_4454_;
}
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_a_4107_);
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4481_ = lean_ctor_get(v___x_4109_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4109_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4109_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref(v_proof_4089_);
lean_dec_ref(v_rhs_4088_);
lean_dec_ref(v_lhs_4087_);
v_a_4489_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4106_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4106_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
v___jp_4102_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_4087_ = stack[0].m_obj;
lean_object* v_rhs_4088_ = stack[1].m_obj;
lean_object* v_proof_4089_ = stack[2].m_obj;
uint8_t v_isHEq_4090_ = stack[3].m_num;
lean_object* v_a_4091_ = stack[4].m_obj;
lean_object* v_a_4092_ = stack[5].m_obj;
lean_object* v_a_4093_ = stack[6].m_obj;
lean_object* v_a_4094_ = stack[7].m_obj;
lean_object* v_a_4095_ = stack[8].m_obj;
lean_object* v_a_4096_ = stack[9].m_obj;
lean_object* v_a_4097_ = stack[10].m_obj;
lean_object* v_a_4098_ = stack[11].m_obj;
lean_object* v_a_4099_ = stack[12].m_obj;
lean_object* v_a_4100_ = stack[13].m_obj;
lean_object* v_res_4497_;
v_res_4497_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4087_, v_rhs_4088_, v_proof_4089_, v_isHEq_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
stack->m_obj
 = v_res_4497_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4498_, lean_object* v_rhs_4499_, lean_object* v_proof_4500_, lean_object* v_isHEq_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
uint8_t v_isHEq_boxed_4513_; lean_object* v_res_4514_; 
v_isHEq_boxed_4513_ = lean_unbox(v_isHEq_4501_);
v_res_4514_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4498_, v_rhs_4499_, v_proof_4500_, v_isHEq_boxed_4513_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec(v_a_4502_);
return v_res_4514_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(lean_object* v_a_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v_toGoalState_4520_; lean_object* v_mvarId_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4557_; 
v___x_4519_ = lean_st_ref_take(v_a_4517_);
v_toGoalState_4520_ = lean_ctor_get(v___x_4519_, 0);
v_mvarId_4521_ = lean_ctor_get(v___x_4519_, 1);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4523_ = v___x_4519_;
v_isShared_4524_ = v_isSharedCheck_4557_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_mvarId_4521_);
lean_inc(v_toGoalState_4520_);
lean_dec(v___x_4519_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4557_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_nextDeclIdx_4525_; lean_object* v_enodeMap_4526_; lean_object* v_exprs_4527_; lean_object* v_parents_4528_; lean_object* v_congrTable_4529_; lean_object* v_appMap_4530_; lean_object* v_indicesFound_4531_; uint8_t v_inconsistent_4532_; lean_object* v_nextIdx_4533_; lean_object* v_newRawFacts_4534_; lean_object* v_facts_4535_; lean_object* v_extThms_4536_; lean_object* v_ematch_4537_; lean_object* v_inj_4538_; lean_object* v_split_4539_; lean_object* v_clean_4540_; lean_object* v_sstates_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4555_; 
v_nextDeclIdx_4525_ = lean_ctor_get(v_toGoalState_4520_, 0);
v_enodeMap_4526_ = lean_ctor_get(v_toGoalState_4520_, 1);
v_exprs_4527_ = lean_ctor_get(v_toGoalState_4520_, 2);
v_parents_4528_ = lean_ctor_get(v_toGoalState_4520_, 3);
v_congrTable_4529_ = lean_ctor_get(v_toGoalState_4520_, 4);
v_appMap_4530_ = lean_ctor_get(v_toGoalState_4520_, 5);
v_indicesFound_4531_ = lean_ctor_get(v_toGoalState_4520_, 6);
v_inconsistent_4532_ = lean_ctor_get_uint8(v_toGoalState_4520_, sizeof(void*)*17);
v_nextIdx_4533_ = lean_ctor_get(v_toGoalState_4520_, 8);
v_newRawFacts_4534_ = lean_ctor_get(v_toGoalState_4520_, 9);
v_facts_4535_ = lean_ctor_get(v_toGoalState_4520_, 10);
v_extThms_4536_ = lean_ctor_get(v_toGoalState_4520_, 11);
v_ematch_4537_ = lean_ctor_get(v_toGoalState_4520_, 12);
v_inj_4538_ = lean_ctor_get(v_toGoalState_4520_, 13);
v_split_4539_ = lean_ctor_get(v_toGoalState_4520_, 14);
v_clean_4540_ = lean_ctor_get(v_toGoalState_4520_, 15);
v_sstates_4541_ = lean_ctor_get(v_toGoalState_4520_, 16);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_toGoalState_4520_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v_toGoalState_4520_, 7);
lean_dec(v_unused_4556_);
v___x_4543_ = v_toGoalState_4520_;
v_isShared_4544_ = v_isSharedCheck_4555_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_sstates_4541_);
lean_inc(v_clean_4540_);
lean_inc(v_split_4539_);
lean_inc(v_inj_4538_);
lean_inc(v_ematch_4537_);
lean_inc(v_extThms_4536_);
lean_inc(v_facts_4535_);
lean_inc(v_newRawFacts_4534_);
lean_inc(v_nextIdx_4533_);
lean_inc(v_indicesFound_4531_);
lean_inc(v_appMap_4530_);
lean_inc(v_congrTable_4529_);
lean_inc(v_parents_4528_);
lean_inc(v_exprs_4527_);
lean_inc(v_enodeMap_4526_);
lean_inc(v_nextDeclIdx_4525_);
lean_dec(v_toGoalState_4520_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4555_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v___x_4545_ = lean_box(0);
v___x_4546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___closed__0));
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 7, v___x_4546_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_nextDeclIdx_4525_);
lean_ctor_set(v_reuseFailAlloc_4554_, 1, v_enodeMap_4526_);
lean_ctor_set(v_reuseFailAlloc_4554_, 2, v_exprs_4527_);
lean_ctor_set(v_reuseFailAlloc_4554_, 3, v_parents_4528_);
lean_ctor_set(v_reuseFailAlloc_4554_, 4, v_congrTable_4529_);
lean_ctor_set(v_reuseFailAlloc_4554_, 5, v_appMap_4530_);
lean_ctor_set(v_reuseFailAlloc_4554_, 6, v_indicesFound_4531_);
lean_ctor_set(v_reuseFailAlloc_4554_, 7, v___x_4546_);
lean_ctor_set(v_reuseFailAlloc_4554_, 8, v_nextIdx_4533_);
lean_ctor_set(v_reuseFailAlloc_4554_, 9, v_newRawFacts_4534_);
lean_ctor_set(v_reuseFailAlloc_4554_, 10, v_facts_4535_);
lean_ctor_set(v_reuseFailAlloc_4554_, 11, v_extThms_4536_);
lean_ctor_set(v_reuseFailAlloc_4554_, 12, v_ematch_4537_);
lean_ctor_set(v_reuseFailAlloc_4554_, 13, v_inj_4538_);
lean_ctor_set(v_reuseFailAlloc_4554_, 14, v_split_4539_);
lean_ctor_set(v_reuseFailAlloc_4554_, 15, v_clean_4540_);
lean_ctor_set(v_reuseFailAlloc_4554_, 16, v_sstates_4541_);
lean_ctor_set_uint8(v_reuseFailAlloc_4554_, sizeof(void*)*17, v_inconsistent_4532_);
v___x_4548_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4550_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4548_);
v___x_4550_ = v___x_4523_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_mvarId_4521_);
v___x_4550_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = lean_st_ref_put(v_a_4517_, v___x_4550_);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4545_);
return v___x_4552_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4517_ = stack[0].m_obj;
lean_object* v_res_4558_;
v_res_4558_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4517_);
stack->m_obj
 = v_res_4558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg___boxed(lean_object* v_a_4559_, lean_object* v_a_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4559_);
lean_dec(v_a_4559_);
return v_res_4561_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v_a_4562_);
return v___x_4573_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4562_ = stack[0].m_obj;
lean_object* v_a_4563_ = stack[1].m_obj;
lean_object* v_a_4564_ = stack[2].m_obj;
lean_object* v_a_4565_ = stack[3].m_obj;
lean_object* v_a_4566_ = stack[4].m_obj;
lean_object* v_a_4567_ = stack[5].m_obj;
lean_object* v_a_4568_ = stack[6].m_obj;
lean_object* v_a_4569_ = stack[7].m_obj;
lean_object* v_a_4570_ = stack[8].m_obj;
lean_object* v_a_4571_ = stack[9].m_obj;
lean_object* v_res_4574_;
v_res_4574_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
stack->m_obj
 = v_res_4574_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___boxed(lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess(v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec(v_a_4575_);
return v_res_4586_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(lean_object* v_a_4587_){
_start:
{
lean_object* v___x_4589_; lean_object* v_toGoalState_4590_; lean_object* v_toProcess_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; 
v___x_4589_ = lean_st_ref_get(v_a_4587_);
v_toGoalState_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc_ref(v_toGoalState_4590_);
lean_dec(v___x_4589_);
v_toProcess_4591_ = lean_ctor_get(v_toGoalState_4590_, 7);
lean_inc_ref(v_toProcess_4591_);
lean_dec_ref(v_toGoalState_4590_);
v___x_4592_ = lean_array_get_size(v_toProcess_4591_);
v___x_4593_ = lean_unsigned_to_nat(1u);
v___x_4594_ = lean_nat_sub(v___x_4592_, v___x_4593_);
v___x_4595_ = lean_nat_dec_lt(v___x_4594_, v___x_4592_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_dec(v___x_4594_);
lean_dec_ref(v_toProcess_4591_);
v___x_4596_ = lean_box(0);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v_toGoalState_4601_; lean_object* v_mvarId_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4637_; 
v___x_4598_ = lean_array_fget(v_toProcess_4591_, v___x_4594_);
lean_dec(v___x_4594_);
lean_dec_ref(v_toProcess_4591_);
v___x_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
v___x_4600_ = lean_st_ref_take(v_a_4587_);
v_toGoalState_4601_ = lean_ctor_get(v___x_4600_, 0);
v_mvarId_4602_ = lean_ctor_get(v___x_4600_, 1);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4600_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4604_ = v___x_4600_;
v_isShared_4605_ = v_isSharedCheck_4637_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_mvarId_4602_);
lean_inc(v_toGoalState_4601_);
lean_dec(v___x_4600_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4637_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v_nextDeclIdx_4606_; lean_object* v_enodeMap_4607_; lean_object* v_exprs_4608_; lean_object* v_parents_4609_; lean_object* v_congrTable_4610_; lean_object* v_appMap_4611_; lean_object* v_indicesFound_4612_; lean_object* v_toProcess_4613_; uint8_t v_inconsistent_4614_; lean_object* v_nextIdx_4615_; lean_object* v_newRawFacts_4616_; lean_object* v_facts_4617_; lean_object* v_extThms_4618_; lean_object* v_ematch_4619_; lean_object* v_inj_4620_; lean_object* v_split_4621_; lean_object* v_clean_4622_; lean_object* v_sstates_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4636_; 
v_nextDeclIdx_4606_ = lean_ctor_get(v_toGoalState_4601_, 0);
v_enodeMap_4607_ = lean_ctor_get(v_toGoalState_4601_, 1);
v_exprs_4608_ = lean_ctor_get(v_toGoalState_4601_, 2);
v_parents_4609_ = lean_ctor_get(v_toGoalState_4601_, 3);
v_congrTable_4610_ = lean_ctor_get(v_toGoalState_4601_, 4);
v_appMap_4611_ = lean_ctor_get(v_toGoalState_4601_, 5);
v_indicesFound_4612_ = lean_ctor_get(v_toGoalState_4601_, 6);
v_toProcess_4613_ = lean_ctor_get(v_toGoalState_4601_, 7);
v_inconsistent_4614_ = lean_ctor_get_uint8(v_toGoalState_4601_, sizeof(void*)*17);
v_nextIdx_4615_ = lean_ctor_get(v_toGoalState_4601_, 8);
v_newRawFacts_4616_ = lean_ctor_get(v_toGoalState_4601_, 9);
v_facts_4617_ = lean_ctor_get(v_toGoalState_4601_, 10);
v_extThms_4618_ = lean_ctor_get(v_toGoalState_4601_, 11);
v_ematch_4619_ = lean_ctor_get(v_toGoalState_4601_, 12);
v_inj_4620_ = lean_ctor_get(v_toGoalState_4601_, 13);
v_split_4621_ = lean_ctor_get(v_toGoalState_4601_, 14);
v_clean_4622_ = lean_ctor_get(v_toGoalState_4601_, 15);
v_sstates_4623_ = lean_ctor_get(v_toGoalState_4601_, 16);
v_isSharedCheck_4636_ = !lean_is_exclusive(v_toGoalState_4601_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4625_ = v_toGoalState_4601_;
v_isShared_4626_ = v_isSharedCheck_4636_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_sstates_4623_);
lean_inc(v_clean_4622_);
lean_inc(v_split_4621_);
lean_inc(v_inj_4620_);
lean_inc(v_ematch_4619_);
lean_inc(v_extThms_4618_);
lean_inc(v_facts_4617_);
lean_inc(v_newRawFacts_4616_);
lean_inc(v_nextIdx_4615_);
lean_inc(v_toProcess_4613_);
lean_inc(v_indicesFound_4612_);
lean_inc(v_appMap_4611_);
lean_inc(v_congrTable_4610_);
lean_inc(v_parents_4609_);
lean_inc(v_exprs_4608_);
lean_inc(v_enodeMap_4607_);
lean_inc(v_nextDeclIdx_4606_);
lean_dec(v_toGoalState_4601_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4636_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4629_; 
v___x_4627_ = lean_array_pop(v_toProcess_4613_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 7, v___x_4627_);
v___x_4629_ = v___x_4625_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_nextDeclIdx_4606_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_enodeMap_4607_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_exprs_4608_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_parents_4609_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_congrTable_4610_);
lean_ctor_set(v_reuseFailAlloc_4635_, 5, v_appMap_4611_);
lean_ctor_set(v_reuseFailAlloc_4635_, 6, v_indicesFound_4612_);
lean_ctor_set(v_reuseFailAlloc_4635_, 7, v___x_4627_);
lean_ctor_set(v_reuseFailAlloc_4635_, 8, v_nextIdx_4615_);
lean_ctor_set(v_reuseFailAlloc_4635_, 9, v_newRawFacts_4616_);
lean_ctor_set(v_reuseFailAlloc_4635_, 10, v_facts_4617_);
lean_ctor_set(v_reuseFailAlloc_4635_, 11, v_extThms_4618_);
lean_ctor_set(v_reuseFailAlloc_4635_, 12, v_ematch_4619_);
lean_ctor_set(v_reuseFailAlloc_4635_, 13, v_inj_4620_);
lean_ctor_set(v_reuseFailAlloc_4635_, 14, v_split_4621_);
lean_ctor_set(v_reuseFailAlloc_4635_, 15, v_clean_4622_);
lean_ctor_set(v_reuseFailAlloc_4635_, 16, v_sstates_4623_);
lean_ctor_set_uint8(v_reuseFailAlloc_4635_, sizeof(void*)*17, v_inconsistent_4614_);
v___x_4629_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4631_; 
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 0, v___x_4629_);
v___x_4631_ = v___x_4604_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_mvarId_4602_);
v___x_4631_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_st_ref_put(v_a_4587_, v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4599_);
return v___x_4633_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4587_ = stack[0].m_obj;
lean_object* v_res_4638_;
v_res_4638_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4587_);
stack->m_obj
 = v_res_4638_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg___boxed(lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4639_);
lean_dec(v_a_4639_);
return v_res_4641_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v_a_4642_);
return v___x_4653_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4642_ = stack[0].m_obj;
lean_object* v_a_4643_ = stack[1].m_obj;
lean_object* v_a_4644_ = stack[2].m_obj;
lean_object* v_a_4645_ = stack[3].m_obj;
lean_object* v_a_4646_ = stack[4].m_obj;
lean_object* v_a_4647_ = stack[5].m_obj;
lean_object* v_a_4648_ = stack[6].m_obj;
lean_object* v_a_4649_ = stack[7].m_obj;
lean_object* v_a_4650_ = stack[8].m_obj;
lean_object* v_a_4651_ = stack[9].m_obj;
lean_object* v_res_4654_;
v_res_4654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
stack->m_obj
 = v_res_4654_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___boxed(lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f(v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec(v_a_4655_);
return v_res_4666_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4667_, lean_object* v_rhs_4668_, lean_object* v_proof_4669_, uint8_t v_isHEq_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
lean_object* v___x_4682_; 
v___x_4682_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4667_, v_rhs_4668_, v_proof_4669_, v_isHEq_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v___x_4683_; 
lean_dec_ref_known(v___x_4682_, 1);
lean_inc(v_a_4680_);
lean_inc_ref(v_a_4679_);
lean_inc(v_a_4678_);
lean_inc_ref(v_a_4677_);
lean_inc(v_a_4676_);
lean_inc_ref(v_a_4675_);
lean_inc(v_a_4674_);
lean_inc_ref(v_a_4673_);
lean_inc(v_a_4672_);
lean_inc(v_a_4671_);
v___x_4683_ = lean_grind_process_to_do(v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
return v___x_4683_;
}
else
{
return v___x_4682_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_4667_ = stack[0].m_obj;
lean_object* v_rhs_4668_ = stack[1].m_obj;
lean_object* v_proof_4669_ = stack[2].m_obj;
uint8_t v_isHEq_4670_ = stack[3].m_num;
lean_object* v_a_4671_ = stack[4].m_obj;
lean_object* v_a_4672_ = stack[5].m_obj;
lean_object* v_a_4673_ = stack[6].m_obj;
lean_object* v_a_4674_ = stack[7].m_obj;
lean_object* v_a_4675_ = stack[8].m_obj;
lean_object* v_a_4676_ = stack[9].m_obj;
lean_object* v_a_4677_ = stack[10].m_obj;
lean_object* v_a_4678_ = stack[11].m_obj;
lean_object* v_a_4679_ = stack[12].m_obj;
lean_object* v_a_4680_ = stack[13].m_obj;
lean_object* v_res_4684_;
v_res_4684_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4667_, v_rhs_4668_, v_proof_4669_, v_isHEq_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
stack->m_obj
 = v_res_4684_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4685_, lean_object* v_rhs_4686_, lean_object* v_proof_4687_, lean_object* v_isHEq_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
uint8_t v_isHEq_boxed_4700_; lean_object* v_res_4701_; 
v_isHEq_boxed_4700_ = lean_unbox(v_isHEq_4688_);
v_res_4701_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4685_, v_rhs_4686_, v_proof_4687_, v_isHEq_boxed_4700_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec(v_a_4689_);
return v_res_4701_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4702_, lean_object* v_rhs_4703_, lean_object* v_proof_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_){
_start:
{
uint8_t v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = 0;
v___x_4717_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4702_, v_rhs_4703_, v_proof_4704_, v___x_4716_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
return v___x_4717_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_4702_ = stack[0].m_obj;
lean_object* v_rhs_4703_ = stack[1].m_obj;
lean_object* v_proof_4704_ = stack[2].m_obj;
lean_object* v_a_4705_ = stack[3].m_obj;
lean_object* v_a_4706_ = stack[4].m_obj;
lean_object* v_a_4707_ = stack[5].m_obj;
lean_object* v_a_4708_ = stack[6].m_obj;
lean_object* v_a_4709_ = stack[7].m_obj;
lean_object* v_a_4710_ = stack[8].m_obj;
lean_object* v_a_4711_ = stack[9].m_obj;
lean_object* v_a_4712_ = stack[10].m_obj;
lean_object* v_a_4713_ = stack[11].m_obj;
lean_object* v_a_4714_ = stack[12].m_obj;
lean_object* v_res_4718_;
v_res_4718_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4702_, v_rhs_4703_, v_proof_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
stack->m_obj
 = v_res_4718_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4719_, lean_object* v_rhs_4720_, lean_object* v_proof_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4719_, v_rhs_4720_, v_proof_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
lean_dec(v_a_4729_);
lean_dec_ref(v_a_4728_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec(v_a_4722_);
return v_res_4733_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4734_, lean_object* v_rhs_4735_, lean_object* v_proof_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
uint8_t v___x_4748_; lean_object* v___x_4749_; 
v___x_4748_ = 1;
v___x_4749_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4734_, v_rhs_4735_, v_proof_4736_, v___x_4748_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
return v___x_4749_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_4734_ = stack[0].m_obj;
lean_object* v_rhs_4735_ = stack[1].m_obj;
lean_object* v_proof_4736_ = stack[2].m_obj;
lean_object* v_a_4737_ = stack[3].m_obj;
lean_object* v_a_4738_ = stack[4].m_obj;
lean_object* v_a_4739_ = stack[5].m_obj;
lean_object* v_a_4740_ = stack[6].m_obj;
lean_object* v_a_4741_ = stack[7].m_obj;
lean_object* v_a_4742_ = stack[8].m_obj;
lean_object* v_a_4743_ = stack[9].m_obj;
lean_object* v_a_4744_ = stack[10].m_obj;
lean_object* v_a_4745_ = stack[11].m_obj;
lean_object* v_a_4746_ = stack[12].m_obj;
lean_object* v_res_4750_;
v_res_4750_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4734_, v_rhs_4735_, v_proof_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_);
stack->m_obj
 = v_res_4750_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4751_, lean_object* v_rhs_4752_, lean_object* v_proof_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4751_, v_rhs_4752_, v_proof_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
lean_dec(v_a_4755_);
lean_dec(v_a_4754_);
return v_res_4765_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; lean_object* v_toGoalState_4770_; lean_object* v_mvarId_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4807_; 
v___x_4769_ = lean_st_ref_take(v_a_4767_);
v_toGoalState_4770_ = lean_ctor_get(v___x_4769_, 0);
v_mvarId_4771_ = lean_ctor_get(v___x_4769_, 1);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4773_ = v___x_4769_;
v_isShared_4774_ = v_isSharedCheck_4807_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_mvarId_4771_);
lean_inc(v_toGoalState_4770_);
lean_dec(v___x_4769_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4807_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v_nextDeclIdx_4775_; lean_object* v_enodeMap_4776_; lean_object* v_exprs_4777_; lean_object* v_parents_4778_; lean_object* v_congrTable_4779_; lean_object* v_appMap_4780_; lean_object* v_indicesFound_4781_; lean_object* v_toProcess_4782_; uint8_t v_inconsistent_4783_; lean_object* v_nextIdx_4784_; lean_object* v_newRawFacts_4785_; lean_object* v_facts_4786_; lean_object* v_extThms_4787_; lean_object* v_ematch_4788_; lean_object* v_inj_4789_; lean_object* v_split_4790_; lean_object* v_clean_4791_; lean_object* v_sstates_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4806_; 
v_nextDeclIdx_4775_ = lean_ctor_get(v_toGoalState_4770_, 0);
v_enodeMap_4776_ = lean_ctor_get(v_toGoalState_4770_, 1);
v_exprs_4777_ = lean_ctor_get(v_toGoalState_4770_, 2);
v_parents_4778_ = lean_ctor_get(v_toGoalState_4770_, 3);
v_congrTable_4779_ = lean_ctor_get(v_toGoalState_4770_, 4);
v_appMap_4780_ = lean_ctor_get(v_toGoalState_4770_, 5);
v_indicesFound_4781_ = lean_ctor_get(v_toGoalState_4770_, 6);
v_toProcess_4782_ = lean_ctor_get(v_toGoalState_4770_, 7);
v_inconsistent_4783_ = lean_ctor_get_uint8(v_toGoalState_4770_, sizeof(void*)*17);
v_nextIdx_4784_ = lean_ctor_get(v_toGoalState_4770_, 8);
v_newRawFacts_4785_ = lean_ctor_get(v_toGoalState_4770_, 9);
v_facts_4786_ = lean_ctor_get(v_toGoalState_4770_, 10);
v_extThms_4787_ = lean_ctor_get(v_toGoalState_4770_, 11);
v_ematch_4788_ = lean_ctor_get(v_toGoalState_4770_, 12);
v_inj_4789_ = lean_ctor_get(v_toGoalState_4770_, 13);
v_split_4790_ = lean_ctor_get(v_toGoalState_4770_, 14);
v_clean_4791_ = lean_ctor_get(v_toGoalState_4770_, 15);
v_sstates_4792_ = lean_ctor_get(v_toGoalState_4770_, 16);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_toGoalState_4770_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4794_ = v_toGoalState_4770_;
v_isShared_4795_ = v_isSharedCheck_4806_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_sstates_4792_);
lean_inc(v_clean_4791_);
lean_inc(v_split_4790_);
lean_inc(v_inj_4789_);
lean_inc(v_ematch_4788_);
lean_inc(v_extThms_4787_);
lean_inc(v_facts_4786_);
lean_inc(v_newRawFacts_4785_);
lean_inc(v_nextIdx_4784_);
lean_inc(v_toProcess_4782_);
lean_inc(v_indicesFound_4781_);
lean_inc(v_appMap_4780_);
lean_inc(v_congrTable_4779_);
lean_inc(v_parents_4778_);
lean_inc(v_exprs_4777_);
lean_inc(v_enodeMap_4776_);
lean_inc(v_nextDeclIdx_4775_);
lean_dec(v_toGoalState_4770_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4806_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4796_ = lean_box(0);
v___x_4797_ = l_Lean_PersistentArray_push___redArg(v_facts_4786_, v_fact_4766_);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 10, v___x_4797_);
v___x_4799_ = v___x_4794_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_nextDeclIdx_4775_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_enodeMap_4776_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_exprs_4777_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_parents_4778_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v_congrTable_4779_);
lean_ctor_set(v_reuseFailAlloc_4805_, 5, v_appMap_4780_);
lean_ctor_set(v_reuseFailAlloc_4805_, 6, v_indicesFound_4781_);
lean_ctor_set(v_reuseFailAlloc_4805_, 7, v_toProcess_4782_);
lean_ctor_set(v_reuseFailAlloc_4805_, 8, v_nextIdx_4784_);
lean_ctor_set(v_reuseFailAlloc_4805_, 9, v_newRawFacts_4785_);
lean_ctor_set(v_reuseFailAlloc_4805_, 10, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4805_, 11, v_extThms_4787_);
lean_ctor_set(v_reuseFailAlloc_4805_, 12, v_ematch_4788_);
lean_ctor_set(v_reuseFailAlloc_4805_, 13, v_inj_4789_);
lean_ctor_set(v_reuseFailAlloc_4805_, 14, v_split_4790_);
lean_ctor_set(v_reuseFailAlloc_4805_, 15, v_clean_4791_);
lean_ctor_set(v_reuseFailAlloc_4805_, 16, v_sstates_4792_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, sizeof(void*)*17, v_inconsistent_4783_);
v___x_4799_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4801_; 
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4799_);
v___x_4801_ = v___x_4773_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_mvarId_4771_);
v___x_4801_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = lean_st_ref_put(v_a_4767_, v___x_4801_);
v___x_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4796_);
return v___x_4803_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fact_4766_ = stack[0].m_obj;
lean_object* v_a_4767_ = stack[1].m_obj;
lean_object* v_res_4808_;
v_res_4808_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4766_, v_a_4767_);
stack->m_obj
 = v_res_4808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4809_, v_a_4810_);
lean_dec(v_a_4810_);
return v_res_4812_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4813_, v_a_4814_);
return v___x_4825_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact_0interp(lean_interpreter_value* stack)
{
lean_object* v_fact_4813_ = stack[0].m_obj;
lean_object* v_a_4814_ = stack[1].m_obj;
lean_object* v_a_4815_ = stack[2].m_obj;
lean_object* v_a_4816_ = stack[3].m_obj;
lean_object* v_a_4817_ = stack[4].m_obj;
lean_object* v_a_4818_ = stack[5].m_obj;
lean_object* v_a_4819_ = stack[6].m_obj;
lean_object* v_a_4820_ = stack[7].m_obj;
lean_object* v_a_4821_ = stack[8].m_obj;
lean_object* v_a_4822_ = stack[9].m_obj;
lean_object* v_a_4823_ = stack[10].m_obj;
lean_object* v_res_4826_;
v_res_4826_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
stack->m_obj
 = v_res_4826_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
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
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4840_, lean_object* v_rhs_4841_, lean_object* v_proof_4842_, lean_object* v_generation_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_){
_start:
{
lean_object* v___x_4855_; 
lean_inc_ref(v_rhs_4841_);
lean_inc_ref(v_lhs_4840_);
v___x_4855_ = l_Lean_Meta_mkEq(v_lhs_4840_, v_rhs_4841_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4867_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc_n(v_a_4856_, 2);
lean_dec_ref_known(v___x_4855_, 1);
v___x_4857_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4856_, v_a_4844_);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4867_ == 0)
{
lean_object* v_unused_4868_; 
v_unused_4868_ = lean_ctor_get(v___x_4857_, 0);
lean_dec(v_unused_4868_);
v___x_4859_ = v___x_4857_;
v_isShared_4860_ = v_isSharedCheck_4867_;
goto v_resetjp_4858_;
}
else
{
lean_dec(v___x_4857_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4867_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
lean_ctor_set_tag(v___x_4859_, 1);
lean_ctor_set(v___x_4859_, 0, v_a_4856_);
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4856_);
v___x_4862_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
lean_object* v___x_4863_; 
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
lean_inc_ref(v___x_4862_);
lean_inc(v_generation_4843_);
lean_inc_ref(v_lhs_4840_);
v___x_4863_ = lean_grind_internalize(v_lhs_4840_, v_generation_4843_, v___x_4862_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v___x_4864_; 
lean_dec_ref_known(v___x_4863_, 1);
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
lean_inc_ref(v_rhs_4841_);
v___x_4864_ = lean_grind_internalize(v_rhs_4841_, v_generation_4843_, v___x_4862_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v___x_4865_; 
lean_dec_ref_known(v___x_4864_, 1);
v___x_4865_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4840_, v_rhs_4841_, v_proof_4842_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
return v___x_4865_;
}
else
{
lean_dec_ref(v_proof_4842_);
lean_dec_ref(v_rhs_4841_);
lean_dec_ref(v_lhs_4840_);
return v___x_4864_;
}
}
else
{
lean_dec_ref(v___x_4862_);
lean_dec(v_generation_4843_);
lean_dec_ref(v_proof_4842_);
lean_dec_ref(v_rhs_4841_);
lean_dec_ref(v_lhs_4840_);
return v___x_4863_;
}
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v_generation_4843_);
lean_dec_ref(v_proof_4842_);
lean_dec_ref(v_rhs_4841_);
lean_dec_ref(v_lhs_4840_);
v_a_4869_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4855_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4855_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addNewEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_4840_ = stack[0].m_obj;
lean_object* v_rhs_4841_ = stack[1].m_obj;
lean_object* v_proof_4842_ = stack[2].m_obj;
lean_object* v_generation_4843_ = stack[3].m_obj;
lean_object* v_a_4844_ = stack[4].m_obj;
lean_object* v_a_4845_ = stack[5].m_obj;
lean_object* v_a_4846_ = stack[6].m_obj;
lean_object* v_a_4847_ = stack[7].m_obj;
lean_object* v_a_4848_ = stack[8].m_obj;
lean_object* v_a_4849_ = stack[9].m_obj;
lean_object* v_a_4850_ = stack[10].m_obj;
lean_object* v_a_4851_ = stack[11].m_obj;
lean_object* v_a_4852_ = stack[12].m_obj;
lean_object* v_a_4853_ = stack[13].m_obj;
lean_object* v_res_4877_;
v_res_4877_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4840_, v_rhs_4841_, v_proof_4842_, v_generation_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
stack->m_obj
 = v_res_4877_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4878_, lean_object* v_rhs_4879_, lean_object* v_proof_4880_, lean_object* v_generation_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4878_, v_rhs_4879_, v_proof_4880_, v_generation_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec_ref(v_a_4888_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec(v_a_4882_);
return v_res_4893_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4894_, lean_object* v_generation_4895_, lean_object* v_p_4896_, uint8_t v_isNeg_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = lean_box(0);
lean_inc(v_a_4907_);
lean_inc_ref(v_a_4906_);
lean_inc(v_a_4905_);
lean_inc_ref(v_a_4904_);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc_ref(v_a_4900_);
lean_inc(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_p_4896_);
v___x_4910_ = lean_grind_internalize(v_p_4896_, v_generation_4895_, v___x_4909_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_dec_ref_known(v___x_4910_, 1);
if (v_isNeg_4897_ == 0)
{
lean_object* v___x_4911_; 
v___x_4911_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4902_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4913_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4911_, 1);
v___x_4913_ = l_Lean_Meta_mkEqTrue(v_proof_4894_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4915_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc(v_a_4914_);
lean_dec_ref_known(v___x_4913_, 1);
v___x_4915_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4896_, v_a_4912_, v_a_4914_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
return v___x_4915_;
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_dec(v_a_4912_);
lean_dec_ref(v_p_4896_);
v_a_4916_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4913_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4913_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_dec_ref(v_p_4896_);
lean_dec_ref(v_proof_4894_);
v_a_4924_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4911_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4911_);
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
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4902_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = l_Lean_Meta_mkEqFalse(v_proof_4894_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4936_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4934_, 1);
v___x_4936_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4896_, v_a_4933_, v_a_4935_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
return v___x_4936_;
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_dec(v_a_4933_);
lean_dec_ref(v_p_4896_);
v_a_4937_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4934_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4934_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
lean_dec_ref(v_p_4896_);
lean_dec_ref(v_proof_4894_);
v_a_4945_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4932_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4932_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4896_);
lean_dec_ref(v_proof_4894_);
return v___x_4910_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_4894_ = stack[0].m_obj;
lean_object* v_generation_4895_ = stack[1].m_obj;
lean_object* v_p_4896_ = stack[2].m_obj;
uint8_t v_isNeg_4897_ = stack[3].m_num;
lean_object* v_a_4898_ = stack[4].m_obj;
lean_object* v_a_4899_ = stack[5].m_obj;
lean_object* v_a_4900_ = stack[6].m_obj;
lean_object* v_a_4901_ = stack[7].m_obj;
lean_object* v_a_4902_ = stack[8].m_obj;
lean_object* v_a_4903_ = stack[9].m_obj;
lean_object* v_a_4904_ = stack[10].m_obj;
lean_object* v_a_4905_ = stack[11].m_obj;
lean_object* v_a_4906_ = stack[12].m_obj;
lean_object* v_a_4907_ = stack[13].m_obj;
lean_object* v_res_4953_;
v_res_4953_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4894_, v_generation_4895_, v_p_4896_, v_isNeg_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
stack->m_obj
 = v_res_4953_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4954_, lean_object* v_generation_4955_, lean_object* v_p_4956_, lean_object* v_isNeg_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
uint8_t v_isNeg_boxed_4969_; lean_object* v_res_4970_; 
v_isNeg_boxed_4969_ = lean_unbox(v_isNeg_4957_);
v_res_4970_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4954_, v_generation_4955_, v_p_4956_, v_isNeg_boxed_4969_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec(v_a_4959_);
lean_dec(v_a_4958_);
return v_res_4970_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4971_, lean_object* v_generation_4972_, lean_object* v_p_4973_, lean_object* v_lhs_4974_, lean_object* v_rhs_4975_, uint8_t v_isNeg_4976_, uint8_t v_isHEq_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
if (v_isNeg_4976_ == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
lean_inc_ref(v_p_4973_);
v___x_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4989_, 0, v_p_4973_);
lean_inc(v_a_4987_);
lean_inc_ref(v_a_4986_);
lean_inc(v_a_4985_);
lean_inc_ref(v_a_4984_);
lean_inc(v_a_4983_);
lean_inc_ref(v_a_4982_);
lean_inc(v_a_4981_);
lean_inc_ref(v_a_4980_);
lean_inc(v_a_4979_);
lean_inc(v_a_4978_);
lean_inc_ref(v___x_4989_);
lean_inc(v_generation_4972_);
lean_inc_ref(v_lhs_4974_);
v___x_4990_ = lean_grind_internalize(v_lhs_4974_, v_generation_4972_, v___x_4989_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v___x_4991_; 
lean_dec_ref_known(v___x_4990_, 1);
lean_inc(v_a_4987_);
lean_inc_ref(v_a_4986_);
lean_inc(v_a_4985_);
lean_inc_ref(v_a_4984_);
lean_inc(v_a_4983_);
lean_inc_ref(v_a_4982_);
lean_inc(v_a_4981_);
lean_inc_ref(v_a_4980_);
lean_inc(v_a_4979_);
lean_inc(v_a_4978_);
lean_inc_ref(v_rhs_4975_);
v___x_4991_ = lean_grind_internalize(v_rhs_4975_, v_generation_4972_, v___x_4989_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec_ref_known(v___x_4991_, 1);
v___x_4992_ = lean_box(0);
v___x_4993_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4973_, v___x_4992_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v___x_4994_; 
lean_dec_ref_known(v___x_4993_, 1);
v___x_4994_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4974_, v_rhs_4975_, v_proof_4971_, v_isHEq_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
return v___x_4994_;
}
else
{
lean_dec_ref(v_rhs_4975_);
lean_dec_ref(v_lhs_4974_);
lean_dec_ref(v_proof_4971_);
return v___x_4993_;
}
}
else
{
lean_dec_ref(v_rhs_4975_);
lean_dec_ref(v_lhs_4974_);
lean_dec_ref(v_p_4973_);
lean_dec_ref(v_proof_4971_);
return v___x_4991_;
}
}
else
{
lean_dec_ref_known(v___x_4989_, 1);
lean_dec_ref(v_rhs_4975_);
lean_dec_ref(v_lhs_4974_);
lean_dec_ref(v_p_4973_);
lean_dec(v_generation_4972_);
lean_dec_ref(v_proof_4971_);
return v___x_4990_;
}
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
lean_dec_ref(v_rhs_4975_);
lean_dec_ref(v_lhs_4974_);
v___x_4995_ = lean_box(0);
lean_inc(v_a_4987_);
lean_inc_ref(v_a_4986_);
lean_inc(v_a_4985_);
lean_inc_ref(v_a_4984_);
lean_inc(v_a_4983_);
lean_inc_ref(v_a_4982_);
lean_inc(v_a_4981_);
lean_inc_ref(v_a_4980_);
lean_inc(v_a_4979_);
lean_inc(v_a_4978_);
lean_inc_ref(v_p_4973_);
v___x_4996_ = lean_grind_internalize(v_p_4973_, v_generation_4972_, v___x_4995_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v___x_4997_; 
lean_dec_ref_known(v___x_4996_, 1);
v___x_4997_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4982_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_4999_; 
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_a_4998_);
lean_dec_ref_known(v___x_4997_, 1);
v___x_4999_ = l_Lean_Meta_mkEqFalse(v_proof_4971_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5001_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref_known(v___x_4999_, 1);
v___x_5001_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4973_, v_a_4998_, v_a_5000_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
return v___x_5001_;
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v_a_4998_);
lean_dec_ref(v_p_4973_);
v_a_5002_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_4999_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_4999_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_dec_ref(v_p_4973_);
lean_dec_ref(v_proof_4971_);
v_a_5010_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4997_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_4997_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_dec_ref(v_p_4973_);
lean_dec_ref(v_proof_4971_);
return v___x_4996_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_4971_ = stack[0].m_obj;
lean_object* v_generation_4972_ = stack[1].m_obj;
lean_object* v_p_4973_ = stack[2].m_obj;
lean_object* v_lhs_4974_ = stack[3].m_obj;
lean_object* v_rhs_4975_ = stack[4].m_obj;
uint8_t v_isNeg_4976_ = stack[5].m_num;
uint8_t v_isHEq_4977_ = stack[6].m_num;
lean_object* v_a_4978_ = stack[7].m_obj;
lean_object* v_a_4979_ = stack[8].m_obj;
lean_object* v_a_4980_ = stack[9].m_obj;
lean_object* v_a_4981_ = stack[10].m_obj;
lean_object* v_a_4982_ = stack[11].m_obj;
lean_object* v_a_4983_ = stack[12].m_obj;
lean_object* v_a_4984_ = stack[13].m_obj;
lean_object* v_a_4985_ = stack[14].m_obj;
lean_object* v_a_4986_ = stack[15].m_obj;
lean_object* v_a_4987_ = stack[16].m_obj;
lean_object* v_res_5018_;
v_res_5018_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4971_, v_generation_4972_, v_p_4973_, v_lhs_4974_, v_rhs_4975_, v_isNeg_4976_, v_isHEq_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
stack->m_obj
 = v_res_5018_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_5019_ = _args[0];
lean_object* v_generation_5020_ = _args[1];
lean_object* v_p_5021_ = _args[2];
lean_object* v_lhs_5022_ = _args[3];
lean_object* v_rhs_5023_ = _args[4];
lean_object* v_isNeg_5024_ = _args[5];
lean_object* v_isHEq_5025_ = _args[6];
lean_object* v_a_5026_ = _args[7];
lean_object* v_a_5027_ = _args[8];
lean_object* v_a_5028_ = _args[9];
lean_object* v_a_5029_ = _args[10];
lean_object* v_a_5030_ = _args[11];
lean_object* v_a_5031_ = _args[12];
lean_object* v_a_5032_ = _args[13];
lean_object* v_a_5033_ = _args[14];
lean_object* v_a_5034_ = _args[15];
lean_object* v_a_5035_ = _args[16];
lean_object* v_a_5036_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_5037_; uint8_t v_isHEq_boxed_5038_; lean_object* v_res_5039_; 
v_isNeg_boxed_5037_ = lean_unbox(v_isNeg_5024_);
v_isHEq_boxed_5038_ = lean_unbox(v_isHEq_5025_);
v_res_5039_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5019_, v_generation_5020_, v_p_5021_, v_lhs_5022_, v_rhs_5023_, v_isNeg_boxed_5037_, v_isHEq_boxed_5038_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
lean_dec(v_a_5029_);
lean_dec_ref(v_a_5028_);
lean_dec(v_a_5027_);
lean_dec(v_a_5026_);
return v_res_5039_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_5043_, lean_object* v_generation_5044_, lean_object* v_p_5045_, uint8_t v_isNeg_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v___x_5058_; 
lean_inc_ref(v_p_5045_);
v___x_5058_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_5045_, v_a_5054_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v___x_5060_; uint8_t v___x_5061_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___x_5060_ = l_Lean_Expr_cleanupAnnotations(v_a_5059_);
v___x_5061_ = l_Lean_Expr_isApp(v___x_5060_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
lean_dec_ref(v___x_5060_);
v___x_5062_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5062_;
}
else
{
lean_object* v_arg_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_arg_5063_ = lean_ctor_get(v___x_5060_, 1);
lean_inc_ref(v_arg_5063_);
v___x_5064_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5060_);
v___x_5065_ = l_Lean_Expr_isApp(v___x_5064_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; 
lean_dec_ref(v___x_5064_);
lean_dec_ref(v_arg_5063_);
v___x_5066_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5066_;
}
else
{
lean_object* v_arg_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; 
v_arg_5067_ = lean_ctor_get(v___x_5064_, 1);
lean_inc_ref(v_arg_5067_);
v___x_5068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5064_);
v___x_5069_ = l_Lean_Expr_isApp(v___x_5068_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; 
lean_dec_ref(v___x_5068_);
lean_dec_ref(v_arg_5067_);
lean_dec_ref(v_arg_5063_);
v___x_5070_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5070_;
}
else
{
lean_object* v_arg_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; uint8_t v___x_5074_; 
v_arg_5071_ = lean_ctor_get(v___x_5068_, 1);
lean_inc_ref(v_arg_5071_);
v___x_5072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5068_);
v___x_5073_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5074_ = l_Lean_Expr_isConstOf(v___x_5072_, v___x_5073_);
if (v___x_5074_ == 0)
{
uint8_t v___x_5075_; 
lean_dec_ref(v_arg_5067_);
v___x_5075_ = l_Lean_Expr_isApp(v___x_5072_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; 
lean_dec_ref(v___x_5072_);
lean_dec_ref(v_arg_5071_);
lean_dec_ref(v_arg_5063_);
v___x_5076_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5076_;
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; 
v___x_5077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5072_);
v___x_5078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5079_ = l_Lean_Expr_isConstOf(v___x_5077_, v___x_5078_);
lean_dec_ref(v___x_5077_);
if (v___x_5079_ == 0)
{
lean_object* v___x_5080_; 
lean_dec_ref(v_arg_5071_);
lean_dec_ref(v_arg_5063_);
v___x_5080_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5080_;
}
else
{
lean_object* v___x_5081_; 
v___x_5081_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5043_, v_generation_5044_, v_p_5045_, v_arg_5071_, v_arg_5063_, v_isNeg_5046_, v___x_5079_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5081_;
}
}
}
else
{
uint8_t v___x_5082_; 
lean_dec_ref(v___x_5072_);
v___x_5082_ = l_Lean_Expr_isProp(v_arg_5071_);
lean_dec_ref(v_arg_5071_);
if (v___x_5082_ == 0)
{
lean_object* v___x_5083_; 
v___x_5083_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5043_, v_generation_5044_, v_p_5045_, v_arg_5067_, v_arg_5063_, v_isNeg_5046_, v___x_5082_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5083_;
}
else
{
lean_object* v___x_5084_; 
lean_dec_ref(v_arg_5067_);
lean_dec_ref(v_arg_5063_);
v___x_5084_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
return v___x_5084_;
}
}
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec_ref(v_p_5045_);
lean_dec(v_generation_5044_);
lean_dec_ref(v_proof_5043_);
v_a_5085_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5058_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5058_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_5043_ = stack[0].m_obj;
lean_object* v_generation_5044_ = stack[1].m_obj;
lean_object* v_p_5045_ = stack[2].m_obj;
uint8_t v_isNeg_5046_ = stack[3].m_num;
lean_object* v_a_5047_ = stack[4].m_obj;
lean_object* v_a_5048_ = stack[5].m_obj;
lean_object* v_a_5049_ = stack[6].m_obj;
lean_object* v_a_5050_ = stack[7].m_obj;
lean_object* v_a_5051_ = stack[8].m_obj;
lean_object* v_a_5052_ = stack[9].m_obj;
lean_object* v_a_5053_ = stack[10].m_obj;
lean_object* v_a_5054_ = stack[11].m_obj;
lean_object* v_a_5055_ = stack[12].m_obj;
lean_object* v_a_5056_ = stack[13].m_obj;
lean_object* v_res_5093_;
v_res_5093_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5043_, v_generation_5044_, v_p_5045_, v_isNeg_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
stack->m_obj
 = v_res_5093_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5094_, lean_object* v_generation_5095_, lean_object* v_p_5096_, lean_object* v_isNeg_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_){
_start:
{
uint8_t v_isNeg_boxed_5109_; lean_object* v_res_5110_; 
v_isNeg_boxed_5109_ = lean_unbox(v_isNeg_5097_);
v_res_5110_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5094_, v_generation_5095_, v_p_5096_, v_isNeg_boxed_5109_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec_ref(v_a_5104_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec(v_a_5098_);
return v_res_5110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5119_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5120_ = l_Lean_Name_append(v___x_5119_, v___x_5118_);
return v___x_5120_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5121_, lean_object* v_proof_5122_, lean_object* v_generation_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v___x_5166_; lean_object* v_toCold_5167_; lean_object* v_options_5168_; uint8_t v_hasTrace_5169_; 
lean_inc_ref(v_fact_5121_);
v___x_5166_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5121_, v_a_5124_);
lean_dec_ref(v___x_5166_);
v_toCold_5167_ = lean_ctor_get(v_a_5132_, 0);
v_options_5168_ = lean_ctor_get(v_toCold_5167_, 2);
v_hasTrace_5169_ = lean_ctor_get_uint8(v_options_5168_, sizeof(void*)*1);
if (v_hasTrace_5169_ == 0)
{
v___y_5149_ = v_a_5124_;
v___y_5150_ = v_a_5125_;
v___y_5151_ = v_a_5126_;
v___y_5152_ = v_a_5127_;
v___y_5153_ = v_a_5128_;
v___y_5154_ = v_a_5129_;
v___y_5155_ = v_a_5130_;
v___y_5156_ = v_a_5131_;
v___y_5157_ = v_a_5132_;
v___y_5158_ = v_a_5133_;
goto v___jp_5148_;
}
else
{
lean_object* v_inheritedTraceOptions_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; 
v_inheritedTraceOptions_5170_ = lean_ctor_get(v_toCold_5167_, 11);
v___x_5171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5170_, v_options_5168_, v___x_5172_);
if (v___x_5173_ == 0)
{
v___y_5149_ = v_a_5124_;
v___y_5150_ = v_a_5125_;
v___y_5151_ = v_a_5126_;
v___y_5152_ = v_a_5127_;
v___y_5153_ = v_a_5128_;
v___y_5154_ = v_a_5129_;
v___y_5155_ = v_a_5130_;
v___y_5156_ = v_a_5131_;
v___y_5157_ = v_a_5132_;
v___y_5158_ = v_a_5133_;
goto v___jp_5148_;
}
else
{
lean_object* v___x_5174_; 
v___x_5174_ = l_Lean_Meta_Grind_updateLastTag(v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
lean_dec_ref_known(v___x_5174_, 1);
lean_inc_ref(v_fact_5121_);
v___x_5175_ = l_Lean_MessageData_ofExpr(v_fact_5121_);
v___x_5176_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5171_, v___x_5175_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_dec_ref_known(v___x_5176_, 1);
v___y_5149_ = v_a_5124_;
v___y_5150_ = v_a_5125_;
v___y_5151_ = v_a_5126_;
v___y_5152_ = v_a_5127_;
v___y_5153_ = v_a_5128_;
v___y_5154_ = v_a_5129_;
v___y_5155_ = v_a_5130_;
v___y_5156_ = v_a_5131_;
v___y_5157_ = v_a_5132_;
v___y_5158_ = v_a_5133_;
goto v___jp_5148_;
}
else
{
lean_dec(v_generation_5123_);
lean_dec_ref(v_proof_5122_);
lean_dec_ref(v_fact_5121_);
return v___x_5176_;
}
}
else
{
lean_dec(v_generation_5123_);
lean_dec_ref(v_proof_5122_);
lean_dec_ref(v_fact_5121_);
return v___x_5174_;
}
}
}
v___jp_5135_:
{
uint8_t v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = 0;
v___x_5147_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5122_, v_generation_5123_, v_fact_5121_, v___x_5146_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
return v___x_5147_;
}
v___jp_5148_:
{
lean_object* v___x_5159_; uint8_t v___x_5160_; 
lean_inc_ref(v_fact_5121_);
v___x_5159_ = l_Lean_Expr_cleanupAnnotations(v_fact_5121_);
v___x_5160_ = l_Lean_Expr_isApp(v___x_5159_);
if (v___x_5160_ == 0)
{
lean_dec_ref(v___x_5159_);
v___y_5136_ = v___y_5149_;
v___y_5137_ = v___y_5150_;
v___y_5138_ = v___y_5151_;
v___y_5139_ = v___y_5152_;
v___y_5140_ = v___y_5153_;
v___y_5141_ = v___y_5154_;
v___y_5142_ = v___y_5155_;
v___y_5143_ = v___y_5156_;
v___y_5144_ = v___y_5157_;
v___y_5145_ = v___y_5158_;
goto v___jp_5135_;
}
else
{
lean_object* v_arg_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v_arg_5161_ = lean_ctor_get(v___x_5159_, 1);
lean_inc_ref(v_arg_5161_);
v___x_5162_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5159_);
v___x_5163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5164_ = l_Lean_Expr_isConstOf(v___x_5162_, v___x_5163_);
lean_dec_ref(v___x_5162_);
if (v___x_5164_ == 0)
{
lean_dec_ref(v_arg_5161_);
v___y_5136_ = v___y_5149_;
v___y_5137_ = v___y_5150_;
v___y_5138_ = v___y_5151_;
v___y_5139_ = v___y_5152_;
v___y_5140_ = v___y_5153_;
v___y_5141_ = v___y_5154_;
v___y_5142_ = v___y_5155_;
v___y_5143_ = v___y_5156_;
v___y_5144_ = v___y_5157_;
v___y_5145_ = v___y_5158_;
goto v___jp_5135_;
}
else
{
lean_object* v___x_5165_; 
lean_dec_ref(v_fact_5121_);
v___x_5165_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5122_, v_generation_5123_, v_arg_5161_, v___x_5164_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
return v___x_5165_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_fact_5121_ = stack[0].m_obj;
lean_object* v_proof_5122_ = stack[1].m_obj;
lean_object* v_generation_5123_ = stack[2].m_obj;
lean_object* v_a_5124_ = stack[3].m_obj;
lean_object* v_a_5125_ = stack[4].m_obj;
lean_object* v_a_5126_ = stack[5].m_obj;
lean_object* v_a_5127_ = stack[6].m_obj;
lean_object* v_a_5128_ = stack[7].m_obj;
lean_object* v_a_5129_ = stack[8].m_obj;
lean_object* v_a_5130_ = stack[9].m_obj;
lean_object* v_a_5131_ = stack[10].m_obj;
lean_object* v_a_5132_ = stack[11].m_obj;
lean_object* v_a_5133_ = stack[12].m_obj;
lean_object* v_res_5177_;
v_res_5177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5121_, v_proof_5122_, v_generation_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_);
stack->m_obj
 = v_res_5177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5178_, lean_object* v_proof_5179_, lean_object* v_generation_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5178_, v_proof_5179_, v_generation_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
lean_dec(v_a_5181_);
return v_res_5192_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5196_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; uint8_t v___x_5209_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v___x_5209_ = lean_unbox(v_a_5208_);
lean_dec(v_a_5208_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5210_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5211_ = l_Lean_Core_checkSystem(v___x_5210_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v___x_5212_; 
lean_dec_ref_known(v___x_5211_, 1);
v___x_5212_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popToProcess_x3f___redArg(v___y_5196_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5260_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5260_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5260_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
if (lean_obj_tag(v_a_5213_) == 1)
{
lean_object* v_val_5217_; 
lean_del_object(v___x_5215_);
v_val_5217_ = lean_ctor_get(v_a_5213_, 0);
lean_inc(v_val_5217_);
lean_dec_ref_known(v_a_5213_, 1);
switch(lean_obj_tag(v_val_5217_))
{
case 0:
{
lean_object* v_lhs_5218_; lean_object* v_rhs_5219_; lean_object* v_proof_5220_; uint8_t v_isHEq_5221_; lean_object* v___x_5222_; 
v_lhs_5218_ = lean_ctor_get(v_val_5217_, 0);
lean_inc_ref(v_lhs_5218_);
v_rhs_5219_ = lean_ctor_get(v_val_5217_, 1);
lean_inc_ref(v_rhs_5219_);
v_proof_5220_ = lean_ctor_get(v_val_5217_, 2);
lean_inc_ref(v_proof_5220_);
v_isHEq_5221_ = lean_ctor_get_uint8(v_val_5217_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5217_, 3);
v___x_5222_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5218_, v_rhs_5219_, v_proof_5220_, v_isHEq_5221_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_dec_ref_known(v___x_5222_, 1);
goto _start;
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
v_a_5224_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_5222_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5222_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
return v___x_5229_;
}
}
}
}
case 1:
{
lean_object* v_prop_5232_; lean_object* v_proof_5233_; lean_object* v_generation_5234_; lean_object* v___x_5235_; 
v_prop_5232_ = lean_ctor_get(v_val_5217_, 0);
lean_inc_ref(v_prop_5232_);
v_proof_5233_ = lean_ctor_get(v_val_5217_, 1);
lean_inc_ref(v_proof_5233_);
v_generation_5234_ = lean_ctor_get(v_val_5217_, 2);
lean_inc(v_generation_5234_);
lean_dec_ref_known(v_val_5217_, 3);
v___x_5235_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5232_, v_proof_5233_, v_generation_5234_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_dec_ref_known(v___x_5235_, 1);
goto _start;
}
else
{
lean_object* v_a_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5244_; 
v_a_5237_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5239_ = v___x_5235_;
v_isShared_5240_ = v_isSharedCheck_5244_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_a_5237_);
lean_dec(v___x_5235_);
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
default: 
{
lean_object* v_e_5245_; lean_object* v___x_5246_; 
v_e_5245_ = lean_ctor_get(v_val_5217_, 0);
lean_inc_ref(v_e_5245_);
lean_dec_ref_known(v_val_5217_, 1);
v___x_5246_ = l_Lean_Meta_Grind_propagateUp(v_e_5245_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_dec_ref_known(v___x_5246_, 1);
goto _start;
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
v_a_5248_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5246_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5246_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
}
else
{
lean_object* v___x_5256_; lean_object* v___x_5258_; 
lean_dec(v_a_5213_);
v___x_5256_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 0, v___x_5256_);
v___x_5258_ = v___x_5215_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5268_; 
v_a_5261_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5263_ = v___x_5212_;
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5212_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5268_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v___x_5266_; 
if (v_isShared_5264_ == 0)
{
v___x_5266_ = v___x_5263_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
}
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
v_a_5269_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5211_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5211_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
else
{
lean_object* v___x_5277_; 
v___x_5277_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetToProcess___redArg(v___y_5196_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5285_; 
v_isSharedCheck_5285_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; 
v_unused_5286_ = lean_ctor_get(v___x_5277_, 0);
lean_dec(v_unused_5286_);
v___x_5279_ = v___x_5277_;
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
else
{
lean_dec(v___x_5277_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5281_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___closed__0));
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v___x_5281_);
v___x_5283_ = v___x_5279_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
v_a_5287_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5277_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5277_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
v_a_5295_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5207_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5207_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
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
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5196_ = stack[0].m_obj;
lean_object* v___y_5197_ = stack[1].m_obj;
lean_object* v___y_5198_ = stack[2].m_obj;
lean_object* v___y_5199_ = stack[3].m_obj;
lean_object* v___y_5200_ = stack[4].m_obj;
lean_object* v___y_5201_ = stack[5].m_obj;
lean_object* v___y_5202_ = stack[6].m_obj;
lean_object* v___y_5203_ = stack[7].m_obj;
lean_object* v___y_5204_ = stack[8].m_obj;
lean_object* v___y_5205_ = stack[9].m_obj;
lean_object* v_res_5303_;
v_res_5303_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
stack->m_obj
 = v_res_5303_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg___boxed(lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
lean_dec(v___y_5311_);
lean_dec_ref(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec(v___y_5304_);
return v_res_5315_;
}
}
lean_object* lean_grind_process_to_do(lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5327_ = lean_box(0);
v___x_5328_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec(v_a_5316_);
if (lean_obj_tag(v___x_5328_) == 0)
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5341_; 
v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5331_ = v___x_5328_;
v_isShared_5332_ = v_isSharedCheck_5341_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5328_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5341_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v_fst_5333_; 
v_fst_5333_ = lean_ctor_get(v_a_5329_, 0);
lean_inc(v_fst_5333_);
lean_dec(v_a_5329_);
if (lean_obj_tag(v_fst_5333_) == 0)
{
lean_object* v___x_5335_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 0, v___x_5327_);
v___x_5335_ = v___x_5331_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5327_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
else
{
lean_object* v_val_5337_; lean_object* v___x_5339_; 
v_val_5337_ = lean_ctor_get(v_fst_5333_, 0);
lean_inc(v_val_5337_);
lean_dec_ref_known(v_fst_5333_, 1);
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 0, v_val_5337_);
v___x_5339_ = v___x_5331_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_val_5337_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
v_a_5342_ = lean_ctor_get(v___x_5328_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5328_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5328_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5328_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
}
LEAN_EXPORT void lean_grind_process_to_do_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5316_ = stack[0].m_obj;
lean_object* v_a_5317_ = stack[1].m_obj;
lean_object* v_a_5318_ = stack[2].m_obj;
lean_object* v_a_5319_ = stack[3].m_obj;
lean_object* v_a_5320_ = stack[4].m_obj;
lean_object* v_a_5321_ = stack[5].m_obj;
lean_object* v_a_5322_ = stack[6].m_obj;
lean_object* v_a_5323_ = stack[7].m_obj;
lean_object* v_a_5324_ = stack[8].m_obj;
lean_object* v_a_5325_ = stack[9].m_obj;
lean_object* v_res_5350_;
v_res_5350_ = lean_grind_process_to_do(v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_);
stack->m_obj
 = v_res_5350_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl___boxed(lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = lean_grind_process_to_do(v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_);
return v_res_5362_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_object* v_inst_5363_, lean_object* v_a_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v___x_5376_; 
v___x_5376_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___redArg(v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
return v___x_5376_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5364_ = stack[1].m_obj;
lean_object* v___y_5365_ = stack[2].m_obj;
lean_object* v___y_5366_ = stack[3].m_obj;
lean_object* v___y_5367_ = stack[4].m_obj;
lean_object* v___y_5368_ = stack[5].m_obj;
lean_object* v___y_5369_ = stack[6].m_obj;
lean_object* v___y_5370_ = stack[7].m_obj;
lean_object* v___y_5371_ = stack[8].m_obj;
lean_object* v___y_5372_ = stack[9].m_obj;
lean_object* v___y_5373_ = stack[10].m_obj;
lean_object* v___y_5374_ = stack[11].m_obj;
lean_object* v_res_5377_;
v_res_5377_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(lean_box(0), v_a_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
stack->m_obj
 = v_res_5377_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0___boxed(lean_object* v_inst_5378_, lean_object* v_a_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processToDoImpl_spec__0(v_inst_5378_, v_a_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v_a_5379_);
return v_res_5391_;
}
}
lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5392_, lean_object* v_proof_5393_, lean_object* v_generation_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
uint8_t v___x_5406_; 
lean_inc_ref(v_fact_5392_);
v___x_5406_ = l_Lean_Expr_isTrue(v_fact_5392_);
if (v___x_5406_ == 0)
{
lean_object* v___x_5407_; 
v___x_5407_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5395_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5438_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5410_ = v___x_5407_;
v_isShared_5411_ = v_isSharedCheck_5438_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5407_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5438_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
uint8_t v___x_5412_; 
v___x_5412_ = lean_unbox(v_a_5408_);
lean_dec(v_a_5408_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; 
lean_del_object(v___x_5410_);
lean_inc(v_a_5404_);
lean_inc_ref(v_a_5403_);
lean_inc(v_a_5402_);
lean_inc_ref(v_a_5401_);
lean_inc(v_a_5400_);
lean_inc_ref(v_a_5399_);
lean_inc(v_a_5398_);
lean_inc_ref(v_a_5397_);
lean_inc(v_a_5396_);
lean_inc(v_a_5395_);
v___x_5413_ = lean_grind_process_to_do(v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v___x_5414_; 
lean_dec_ref_known(v___x_5413_, 1);
v___x_5414_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5395_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5425_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5417_ = v___x_5414_;
v_isShared_5418_ = v_isSharedCheck_5425_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5414_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5425_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
uint8_t v___x_5419_; 
v___x_5419_ = lean_unbox(v_a_5415_);
lean_dec(v_a_5415_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; 
lean_del_object(v___x_5417_);
v___x_5420_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5392_, v_proof_5393_, v_generation_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_);
return v___x_5420_;
}
else
{
lean_object* v___x_5421_; lean_object* v___x_5423_; 
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
v___x_5421_ = lean_box(0);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 0, v___x_5421_);
v___x_5423_ = v___x_5417_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
v_a_5426_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5414_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5414_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
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
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
return v___x_5413_;
}
}
else
{
lean_object* v___x_5434_; lean_object* v___x_5436_; 
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
v___x_5434_ = lean_box(0);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 0, v___x_5434_);
v___x_5436_ = v___x_5410_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
v_a_5439_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5407_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5407_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
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
lean_object* v___x_5447_; lean_object* v___x_5448_; 
lean_dec(v_generation_5394_);
lean_dec_ref(v_proof_5393_);
lean_dec_ref(v_fact_5392_);
v___x_5447_ = lean_box(0);
v___x_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5448_, 0, v___x_5447_);
return v___x_5448_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_add_0interp(lean_interpreter_value* stack)
{
lean_object* v_fact_5392_ = stack[0].m_obj;
lean_object* v_proof_5393_ = stack[1].m_obj;
lean_object* v_generation_5394_ = stack[2].m_obj;
lean_object* v_a_5395_ = stack[3].m_obj;
lean_object* v_a_5396_ = stack[4].m_obj;
lean_object* v_a_5397_ = stack[5].m_obj;
lean_object* v_a_5398_ = stack[6].m_obj;
lean_object* v_a_5399_ = stack[7].m_obj;
lean_object* v_a_5400_ = stack[8].m_obj;
lean_object* v_a_5401_ = stack[9].m_obj;
lean_object* v_a_5402_ = stack[10].m_obj;
lean_object* v_a_5403_ = stack[11].m_obj;
lean_object* v_a_5404_ = stack[12].m_obj;
lean_object* v_res_5449_;
v_res_5449_ = l_Lean_Meta_Grind_add(v_fact_5392_, v_proof_5393_, v_generation_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_);
stack->m_obj
 = v_res_5449_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5450_, lean_object* v_proof_5451_, lean_object* v_generation_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Lean_Meta_Grind_add(v_fact_5450_, v_proof_5451_, v_generation_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
lean_dec(v_a_5462_);
lean_dec_ref(v_a_5461_);
lean_dec(v_a_5460_);
lean_dec_ref(v_a_5459_);
lean_dec(v_a_5458_);
lean_dec_ref(v_a_5457_);
lean_dec(v_a_5456_);
lean_dec_ref(v_a_5455_);
lean_dec(v_a_5454_);
lean_dec(v_a_5453_);
return v_res_5464_;
}
}
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5465_, lean_object* v_generation_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_){
_start:
{
lean_object* v___x_5478_; 
lean_inc(v_fvarId_5465_);
v___x_5478_ = l_Lean_FVarId_getType___redArg(v_fvarId_5465_, v_a_5473_, v_a_5475_, v_a_5476_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v_a_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc(v_a_5479_);
lean_dec_ref_known(v___x_5478_, 1);
v___x_5480_ = l_Lean_mkFVar(v_fvarId_5465_);
v___x_5481_ = l_Lean_Meta_Grind_add(v_a_5479_, v___x_5480_, v_generation_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
return v___x_5481_;
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec(v_generation_5466_);
lean_dec(v_fvarId_5465_);
v_a_5482_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5478_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5478_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_addHypothesis_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_5465_ = stack[0].m_obj;
lean_object* v_generation_5466_ = stack[1].m_obj;
lean_object* v_a_5467_ = stack[2].m_obj;
lean_object* v_a_5468_ = stack[3].m_obj;
lean_object* v_a_5469_ = stack[4].m_obj;
lean_object* v_a_5470_ = stack[5].m_obj;
lean_object* v_a_5471_ = stack[6].m_obj;
lean_object* v_a_5472_ = stack[7].m_obj;
lean_object* v_a_5473_ = stack[8].m_obj;
lean_object* v_a_5474_ = stack[9].m_obj;
lean_object* v_a_5475_ = stack[10].m_obj;
lean_object* v_a_5476_ = stack[11].m_obj;
lean_object* v_res_5490_;
v_res_5490_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5465_, v_generation_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
stack->m_obj
 = v_res_5490_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5491_, lean_object* v_generation_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_){
_start:
{
lean_object* v_res_5504_; 
v_res_5504_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5491_, v_generation_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
lean_dec_ref(v_a_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v_a_5497_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec(v_a_5493_);
return v_res_5504_;
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
